import Mathlib

-- Disclaimer 1: This week's homework is essentially based on exercises
-- on "Mathematics in Lean" by Jeremy Avigad & Patrick Massot

-- Disclaimer 2: I may add one or two exercises on Topological spaces later on
-- (from MIL as well) but I wanted you to get started if you wanted.

-- The (soft) deadline is 2 weeks from today (i.e Tuesday december 9).

-- # Linear Algebra

variable {K : Type*} [Field K]
         {V W : Type*}
         [AddCommGroup V] [Module K V]
         [AddCommGroup W] [Module K W]
         {φ : V →ₗ[K] W}
         (E : Submodule K V)


section LinearAlgebraHW
open Polynomial Module LinearMap End

#check Submodule.add_mem_sup
#check map_mul
#check End.mul_apply
#check LinearMap.ker_le_ker_comp


-- ## Quotient Spaces
-- We didn't have enough time to do quotient spaces in classe: Now is your time to shine!
-- Read the corresponding section (10.2.5) from Mathematics in Lean, and do the exercises
-- (I copy them below for convenience, but it's a lot easier if you read the sections...)

example (E : Submodule K V) (F : Submodule K W) :
    Submodule.map φ E ≤ F ↔ E ≤ Submodule.comap φ F := by
  sorry

example : Submodule K (V ⧸ E) ≃ { F : Submodule K V // E ≤ F } where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry


-- ## Endomorphisms as a 𝕂-algebra

example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) :
    ker (aeval φ P) ⊔ ker (aeval φ Q) = ker (aeval φ (P*Q)) := by
  sorry

-- ## One about using basis
-- Prove that the determinant of an endomorphism is well defined:

#check Matrix.det_mul
#check Matrix.det_one

variable {ι : Type*} (B : Basis ι K V) [Fintype ι] [DecidableEq ι]

example [Fintype ι] (B' : Basis ι K V) (ψ : End K V) :
    (toMatrix B B ψ).det = (toMatrix B' B' ψ).det := by
  set M := toMatrix B B ψ
  set M' := toMatrix B' B' ψ
  set P := (toMatrix B B') LinearMap.id
  set P' := (toMatrix B' B) LinearMap.id
  sorry

end LinearAlgebraHW



-- # Metric Spaces: The Baire Category theorem
section MetricSpacesHW
/-
  In this homework you will complete a proof of the Baire theorem for metric spaces,
  following "Mathematics in Lean". The first one is on the easy side, the second
  one on the hard side!
-/
variable {X : Type*} [MetricSpace X] (a b c : X)

/-
## Step 1: Cauchy sequences
-/

theorem cauchySeq_of_le_geometric_two' {u : ℕ → X}
    (hu : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ (1 / 2) ^ n) : CauchySeq u := by
  rw [Metric.cauchySeq_iff']
  intro ε ε_pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / 2 ^ N * 2 < ε := by sorry
  use N
  intro n hn
  obtain ⟨k, rfl : n = N + k⟩ := le_iff_exists_add.mp hn
  calc
    dist (u (N + k)) (u N) = dist (u (N + 0)) (u (N + k)) := sorry
    _ ≤ ∑ i  ∈ Finset.range k, dist (u (N + i)) (u (N + (i + 1))) := sorry
    _ ≤ ∑ i  ∈ Finset.range k, (1 / 2 : ℝ) ^ (N + i) := sorry
    _ = 1 / 2 ^ N * ∑ i  ∈ Finset.range k, (1 / 2 : ℝ) ^ i := sorry
    _ ≤ 1 / 2 ^ N * 2 := sorry
    _ < ε := sorry


open Metric
-- Remember that in class we saw some variation of
#check mem_closure_iff_seq_limit
-- in classs

example [CompleteSpace X] (f : ℕ → Set X) (ho : ∀ n, IsOpen (f n)) (hd : ∀ n, Dense (f n)) :
    Dense (⋂ n, f n) := by
  let B : ℕ → ℝ := fun n ↦ (1 / 2) ^ n
  have Bpos : ∀ n, 0 < B n
  sorry
  /- Translate the density assumption into two functions `center` and `radius` associating
    to any n, x, δ, δpos a center and a positive radius such that
    `closedBall center radius` is included both in `f n` and in `closedBall x δ`.
    We can also require `radius ≤ (1/2)^(n+1)`, to ensure we get a Cauchy sequence later. -/
  have :
    ∀ (n : ℕ) (x : X),
      ∀ δ > 0, ∃ y : X, ∃ r > 0, r ≤ B (n + 1) ∧ closedBall y r ⊆ closedBall x δ ∩ f n :=
    by sorry
  choose! center radius Hpos HB Hball using this
  intro x
  rw [mem_closure_iff_nhds_basis nhds_basis_closedBall]
  intro ε εpos
  /- `ε` is positive. We have to find a point in the ball of radius `ε` around `x`
    belonging to all `f n`. For this, we construct inductively a sequence
    `F n = (c n, r n)` such that the closed ball `closedBall (c n) (r n)` is included
    in the previous ball and in `f n`, and such that `r n` is small enough to ensure
    that `c n` is a Cauchy sequence. Then `c n` converges to a limit which belongs
    to all the `f n`. -/
  let F : ℕ → X × ℝ := fun n ↦
    Nat.recOn n (Prod.mk x (min ε (B 0)))
      fun n p ↦ Prod.mk (center n p.1 p.2) (radius n p.1 p.2)
  let c : ℕ → X := fun n ↦ (F n).1
  let r : ℕ → ℝ := fun n ↦ (F n).2
  have rpos : ∀ n, 0 < r n := by sorry
  have rB : ∀ n, r n ≤ B n := by sorry
  have incl : ∀ n, closedBall (c (n + 1)) (r (n + 1)) ⊆ closedBall (c n) (r n) ∩ f n := by
    sorry
  have cdist : ∀ n, dist (c n) (c (n + 1)) ≤ B n := by sorry
  have : CauchySeq c := cauchySeq_of_le_geometric_two' cdist
  -- as the sequence `c n` is Cauchy in a complete space, it converges to a limit `y`.
  rcases cauchySeq_tendsto_of_complete this with ⟨y, ylim⟩
  -- this point `y` will be the desired point. We will check that it belongs to all
  -- `f n` and to `ball x ε`.
  use y
  have I : ∀ n, ∀ m ≥ n, closedBall (c m) (r m) ⊆ closedBall (c n) (r n) := by sorry
  have yball : ∀ n, y ∈ closedBall (c n) (r n) := by sorry
  sorry
