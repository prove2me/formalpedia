-- Prove2me | Theorems.Thm_SNumbers_max_gelfandNumber_kolmogorovNumber_le_e_mul_bernsteinNumber
-- name    : SNumbers.max_gelfandNumber_kolmogorovNumber_le_e_mul_bernsteinNumber
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:21:29.969466+00:00
-- url     : https://prove2.me/theorems/1870ef2f-12b1-498a-96db-ced3f6197f19
-- title:
--   SNumbers: max gelfand Number kolmogorov Number le e mul bernstein Number
-- statement:
--   **The Mityagin–Henkin conjecture, up to the constant `e`.** The Gelfand
--   and Kolmogorov numbers are bounded by the Bernstein numbers:
--   `max(cₙ(S), dₙ(S)) ≤ e·(n+1)·bₙ(S)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L967-L972
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L967-L972

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

theorem SNumbers.max_gelfandNumber_kolmogorovNumber_le_e_mul_bernsteinNumber
    (S : X →L[𝕜] Y) (n : ℕ) :
    max (gelfandNumber S n) (kolmogorovNumber S n)
      ≤ Real.exp 1 * ((n : ℝ) + 1) * bernsteinNumber S n := by sorry
