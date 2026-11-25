-- Prove2me | Theorems.Thm_SNumbers_gelfandNumber_add_le
-- name    : SNumbers.gelfandNumber_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:05:42.765023+00:00
-- url     : https://prove2.me/theorems/ea01cac2-945e-592a-be5e-b8c7b7bff55c
-- title:
--   SNumbers: gelfand Number add le
-- statement:
--   (S2) `c_n (S + T) ≤ c_n S + ‖T‖`: additivity with `m = 0`, since `c_0 T = ‖T‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L393-L396
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L393-L396

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

theorem SNumbers.gelfandNumber_add_le (S T : X →L[𝕜] Y) (n : ℕ) :
    gelfandNumber (S + T) n ≤ gelfandNumber S n + ‖T‖ := by sorry
