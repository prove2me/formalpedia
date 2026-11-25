-- Prove2me | Theorems.Thm_SNumbers_hilbertNumber_zero_eq_norm
-- name    : SNumbers.hilbertNumber_zero_eq_norm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:18:41.728809+00:00
-- url     : https://prove2.me/theorems/55a09b49-9a50-4f3b-92af-8502ff015031
-- title:
--   SNumbers: hilbert Number zero eq norm
-- statement:
--   (S1a) `h_0 S = ‖S‖`: the upper half is the easy bound `h_0 S ≤ ‖S‖`, the lower
--   half is `norm_le_hilbertNumber_zero`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Hilbert.lean#L289-L293
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Hilbert.lean#L289-L293

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Definitions.Def_SNumbers_Hilbert
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y W Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem SNumbers.hilbertNumber_zero_eq_norm (S : X →L[𝕜] Y) : hilbertNumber S 0 = ‖S‖ := by sorry
