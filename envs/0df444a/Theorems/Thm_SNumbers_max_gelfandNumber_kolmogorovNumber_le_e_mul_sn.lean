-- Prove2me | Theorems.Thm_SNumbers_max_gelfandNumber_kolmogorovNumber_le_e_mul_sn
-- name    : SNumbers.max_gelfandNumber_kolmogorovNumber_le_e_mul_sn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:46:56.12344+00:00
-- url     : https://prove2.me/theorems/d6c43455-49ff-429e-9edf-e2ae3f2ee3f4
-- title:
--   SNumbers: max gelfand Number kolmogorov Number le e mul sn
-- statement:
--   **The bound for the Gelfand and Kolmogorov numbers.** Both are s-number
--   sequences, so both are bounded by `aₙ`, to which
--   `approximationNumber_le_e_mul_sn` applies:
--   `max(cₙ(S), dₙ(S)) ≤ e·(n+1)·sₙ(S)` for every s-number sequence `s`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L945-L953
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L945-L953

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

theorem SNumbers.max_gelfandNumber_kolmogorovNumber_le_e_mul_sn {s : Family 𝕜}
    (hs : IsSNumberSequence s) (S : X →L[𝕜] Y) (n : ℕ) :
    max (gelfandNumber S n) (kolmogorovNumber S n)
      ≤ Real.exp 1 * ((n : ℝ) + 1) * s S n := by sorry
