import Mathlib.Tactic
import Mathlib.Topology.Instances.Real.Lemmas


open Set Filter Topology

section

-- # Definitions

variable {X : Type*} [TopologicalSpace X]

example {ι : Type*} [Fintype ι] {s : ι → Set X} (hs : ∀ i, IsOpen (s i)) :  IsOpen (⋂ i, s i) :=
  isOpen_iInter_of_finite hs

variable {Y : Type*} [TopologicalSpace Y]

--  ## Continuous functions

example {f : X → Y} : Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s) := continuous_def

example {f : X → Y} {x : X} : ContinuousAt f x ↔ map f (𝓝 x) ≤ 𝓝 (f x) := Iff.rfl

example {f : X → Y} {x : X} : ContinuousAt f x ↔ ∀ U ∈ 𝓝 (f x), ∀ᶠ x in 𝓝 x, f x ∈ U := Iff.rfl

-- ## Building Open Sets from Neighborhoods and viceversa

-- Neighborhoods defined from open sets
example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ t, t ⊆ s ∧ IsOpen t ∧ x ∈ t := mem_nhds_iff

-- The set of all sets containing x is denoted by pure x
example (x : X) : pure x ≤ 𝓝 x := pure_le_nhds x

-- ### Axioms of open sets

-- x is contained in every neigborhood of x
example (x : X) (P : X → Prop) (h : ∀ᶠ y in 𝓝 x, P y) : P x :=  h.self_of_nhds

-- if P holds in a neighborhood of x, there is a neighborhood N' of x such that
-- for all y in N', P holds in a neighborhood of y

example {P : X → Prop} {x : X} (h : ∀ᶠ y in 𝓝 x, P y) : ∀ᶠ y in 𝓝 x, ∀ᶠ z in 𝓝 y, P z :=
  eventually_eventually_nhds.mpr h

-- O is open if ∀ x : O, O ∈ 𝓝 x
#check TopologicalSpace.mkOfNhds

-- When do neighborhoods come from a topology? "S ∈ 𝓝 x ↔ ∃ O, isOpen O ∧ O ⊆ S"
#check TopologicalSpace.nhds_mkOfNhds

-- let's prove it ourselves
example {α : Type*} (n : α → Filter α) (H₀ : ∀ a, pure a ≤ n a)
    (H : ∀ a : α, ∀ p : α → Prop, (∀ᶠ x in n a, p x) → ∀ᶠ y in n a, ∀ᶠ x in n y, p x) :
    ∀ a, ∀ s ∈ n a, ∃ t ∈ n a, t ⊆ s ∧ ∀ a' ∈ t, s ∈ n a' := by
    intro a s hs_neigh_a
    specialize H a s hs_neigh_a
    use {y | ∀ᶠ x in n y, s x}
    use H
    constructor
    · intro y hy
      apply H₀
      apply hy
    · intro a ha
      simp at ha
      exact ha









-- ## Neighborhoods vs Open Sets

#check HasBasis.tendsto_iff
#check nhds_basis_opens
#check isOpen_iff_mem_nhds

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} :
    Continuous f ↔ ∀ x, ContinuousAt f x := by
    constructor
    · intro hcont x
      apply (HasBasis.tendsto_iff (nhds_basis_opens x) (nhds_basis_opens (f x))).mpr
      rintro ib ⟨x_ib, ib_open⟩
      have preimage_open := hcont.isOpen_preimage ib ib_open
      use (f⁻¹' ib)
      tauto
    · intro cont_at_all
      constructor
      intro s s_open
      apply isOpen_iff_mem_nhds.mpr
      intro x hx
      specialize cont_at_all x
      apply cont_at_all
      apply isOpen_iff_mem_nhds.mp s_open
      exact hx



-- # Induced and co-induced topologies


example (f : X → Y) : TopologicalSpace X → TopologicalSpace Y :=
  TopologicalSpace.coinduced f

example (f : X → Y) : TopologicalSpace Y → TopologicalSpace X :=
  TopologicalSpace.induced f

-- ## Order of topologies

-- The order of topologies is the opposite as "usual"
example {T T' : TopologicalSpace X} : T ≤ T' ↔ ∀ s, T'.IsOpen s → T.IsOpen s :=
  Iff.rfl

-- They form the usual "Galois Connection"

example (f : X → Y) (T_X : TopologicalSpace X) (T_Y : TopologicalSpace Y) :
    TopologicalSpace.coinduced f T_X ≤ T_Y ↔ T_X ≤ TopologicalSpace.induced f T_Y :=
  coinduced_le_iff_le_induced

-- And are stable under composition

#check coinduced_compose

#check induced_compose


-- # T1-T4 topologies in HW (TBA)

-- # Compactness

-- x is a cluster point with respect to a filter F if it Neigh intersects F nontrivially.
#check ClusterPt


example [FirstCountableTopology X] {s : Set X} {u : ℕ → X} (hs : IsCompact s)
    (hu : ∀ n, u n ∈ s) : ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a) :=
  hs.tendsto_subseq hu

variable [TopologicalSpace Y]

#check ClusterPt.map


-- we will prove this ourselves
#check Filter.Tendsto.inf
example {x : X} {F : Filter X} {G : Filter Y} (H : ClusterPt x F) {f : X → Y}
    (hfx : ContinuousAt f x) (hf : Tendsto f F G) : ClusterPt (f x) G :=
  by
  have h:= Filter.Tendsto.inf hfx hf
  apply NeBot.mono ?_ h
  apply map_neBot (hf:= H)




-- A set is compact if every non-empty subset admits a cluster point
#check IsCompact

#check NeBot.of_map
-- Hint: You have to consider the filter 𝓟 s ⊓ comap f F
-- map f (𝓟 s ⊓ comap f F) = 𝓟 (f '' s) ⊓ F
example [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {s : Set X} (hs : IsCompact s) :
    IsCompact (f '' s) := by
    intro F hF F_small
    have intersection: map f (𝓟 s ⊓ comap f F) = 𝓟 (f '' s) ⊓ F := by
      rw [@Filter.push_pull, @map_principal]
    have comap_nonempty: (𝓟 s ⊓ comap f F).NeBot := by
      refine neBot_inf_comap_iff_map.mpr ?_
      rw [@map_principal]
      have : 𝓟 (f '' s) ⊓ F = F := by simp_all only [le_principal_iff, inf_of_le_right]
      rw[this]
      exact hF
    have comap_contained : 𝓟 s ⊓ comap f F  ≤ 𝓟 s := by simp only [inf_le_left]
    rcases hs comap_contained with ⟨x, contained,hx⟩
    use f x
    constructor
    · tauto
    · exact hx.map hf.continuousAt (tendsto_inf_right tendsto_comap)








end
