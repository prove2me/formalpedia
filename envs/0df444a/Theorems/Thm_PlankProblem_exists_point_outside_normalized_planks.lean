-- Prove2me | Theorems.Thm_PlankProblem_exists_point_outside_normalized_planks
-- name    : PlankProblem.exists_point_outside_normalized_planks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:47:11.911922+00:00
-- url     : https://prove2.me/theorems/02b56e56-02f5-4ce4-9047-cb0ca8600dde
-- title:
--   Plank Problem: exists point outside normalized planks
-- statement:
--   The normalised form of Ball's theorem, obtained from the core theorem as in the warm-up.
--   Let `K0` be a convex set symmetric about `0`, and let `φᵢ` be linear functionals with points
--   `vᵢ ∈ K0` such that `φᵢ(vᵢ) = 1`.  If the closed slabs
--   `{αᵢ ≤ φᵢ ≤ βᵢ}` have total half-length `∑ (βᵢ - αᵢ)/2 < 1`, then some point of `K0` lies outside
--   all of them.
--
--   Proof: split slab `i` into `kᵢ = ⌊wᵢ N⌋ + 1` overlapping slabs of relative width `≤ 1/N`
--   (with `wᵢ = (βᵢ-αᵢ)/2`), where `N` is so large that the total number `M = ∑ kᵢ ≤ N`.
--   Pull back along `T : ℝ^M → ℝⁿ`, `T eⱼ = v_{i(j)} / M`; the ball of radius `√M` is mapped into the
--   cross-polytope `conv{±vᵢ} ⊆ K0`, and the core theorem gives a point avoiding all small slabs.
--
--   Source: https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/BallPlankFinal.lean#L367-L444
-- source:
--   https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/BallPlankFinal.lean#L367-L444

module
public import Definitions.Def_BallPlank_ShiftedPlanks
public import Definitions.Def_BallPlank_BallPlankFinal
set_option autoImplicit true
@[expose] public section
public section
open Set
open scoped BigOperators InnerProductSpace Pointwise
noncomputable section
open PlankProblem
variable {n : ℕ}
local notation "Rn" => EuclideanSpace ℝ (Fin n)

theorem PlankProblem.exists_point_outside_normalized_planks {m : ℕ} {K0 : Set Rn} (hconv : Convex ℝ K0)
    (h0 : (0 : Rn) ∈ K0) (hneg : ∀ x ∈ K0, -x ∈ K0)
    (φ : Fin m → (Rn →ₗ[ℝ] ℝ)) (v : Fin m → Rn) (hv : ∀ i, v i ∈ K0)
    (hφv : ∀ i, φ i (v i) = 1)
    (α β : Fin m → ℝ) (hαβ : ∀ i, α i ≤ β i) (hsum : ∑ i, (β i - α i) / 2 < 1) :
    ∃ y ∈ K0, ∀ i, φ i y < α i ∨ β i < φ i y := by sorry
