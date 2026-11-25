-- Prove2me | Theorems.Thm_SNumbers_gelfandNumber_le_norm
-- name    : SNumbers.gelfandNumber_le_norm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:01:38.782801+00:00
-- url     : https://prove2.me/theorems/e50b3c5b-058c-447b-aabc-0b019639873f
-- title:
--   SNumbers: gelfand Number le norm
-- statement:
--   Upper bound by the operator norm: `c_n S ≤ ‖S‖`, since `c_n S ≤ c_0 S = ‖S‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L216-L219
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L216-L219

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Gelfand
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem SNumbers.gelfandNumber_le_norm (S : X →L[𝕜] Y) (n : ℕ) :
    gelfandNumber S n ≤ ‖S‖ := by sorry
