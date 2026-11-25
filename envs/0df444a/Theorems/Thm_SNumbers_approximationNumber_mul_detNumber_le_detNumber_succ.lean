-- Prove2me | Theorems.Thm_SNumbers_approximationNumber_mul_detNumber_le_detNumber_succ
-- name    : SNumbers.approximationNumber_mul_detNumber_le_detNumber_succ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:37:02.296542+00:00
-- url     : https://prove2.me/theorems/1156a35a-256a-4bad-8da9-368e75ec7bdc
-- title:
--   SNumbers: approximation Number mul det Number le det Number succ
-- statement:
--   **Growth lemma.** For every `S` and every `k`,
--
--     `(kᵏ/(k+1)^{k+1}) · aₖ(S) · Δₖ(S) ≤ Δₖ₊₁(S)`.
--
--   Fix an admissible pair `(A, B)` for `Δₖ(S)` and put `T := B∘S∘A`. If
--   `det T = 0` there is nothing to prove. Otherwise `T` is invertible, so
--
--     `L := S∘A∘T⁻¹∘B∘S`
--
--   factors through `ℓ₂ᵏ`, hence has rank at most `k`, hence `‖S - L‖ ≥ aₖ(S)`.
--   Pick `x ∈ B_X` with `‖(S - L)x‖` almost `‖S - L‖` and a norming functional
--   `b ∈ B_{Y'}`, and border the pair by them:
--
--     `A₀(ξ ⊕ τ) = λ·Aξ + μ·τ·x`,   `B₀ y = (λ·By) ⊕ (μ·b y)`,
--
--   with `λ² + μ² = 1`, which is again a contraction pair, now for `Δₖ₊₁(S)`. Above
--   the corner, the last column of the matrix of `B₀SA₀` is the combination of the
--   first `k` columns with coefficients `(μ/λ)·ζ`, where `ζ := T⁻¹B(Sx)`, so
--   `Matrix.det_eq_corner_mul_det_submatrix` gives
--
--     `det (B₀SA₀) = λ^{2k}·μ²·b((S - L)x)·det T`.
--
--   The weights `λ² = k/(k+1)`, `μ² = 1/(k+1)` maximise `λ^{2k}μ²`, whose value is
--   then exactly `kᵏ/(k+1)^{k+1}`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L632-L841
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L632-L841

module
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_MaxDifference
set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open scoped Pointwise
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem SNumbers.approximationNumber_mul_detNumber_le_detNumber_succ (S : X →L[𝕜] Y) (k : ℕ) :
    (k : ℝ) ^ k / ((k : ℝ) + 1) ^ (k + 1) * approximationNumber S k * detNumber S k
      ≤ detNumber S (k + 1) := by sorry
