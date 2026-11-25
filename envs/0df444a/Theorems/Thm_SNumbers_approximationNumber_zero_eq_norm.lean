-- Prove2me | Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
-- name    : SNumbers.approximationNumber_zero_eq_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:39:10.870944+00:00
-- url     : https://prove2.me/theorems/d1fc2943-d732-4b4b-b438-6c76318abc96
-- title:
--   SNumbers: approximation Number zero eq norm
-- statement:
--   (S1a) `a_0 S = ‖S‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L137-L139
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L137-L139

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Approximation
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

theorem SNumbers.approximationNumber_zero_eq_norm (S : X →L[𝕜] Y) :
    approximationNumber S 0 = ‖S‖ := by sorry
