-- Prove2me | Theorems.Thm_SNumbers_approximationSet_zero
-- name    : SNumbers.approximationSet_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:56:07.344408+00:00
-- url     : https://prove2.me/theorems/bb420bca-3825-4446-9aa7-7fe6686db5eb
-- title:
--   SNumbers: approximation Set zero
-- statement:
--   The approximation set at `n = 0` is the singleton `{‖S‖}`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L127-L134
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L127-L134

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

theorem SNumbers.approximationSet_zero (S : X →L[𝕜] Y) :
    approximationSet S 0 = {‖S‖} := by sorry
