-- Prove2me | Theorems.Thm_SNumbers_deviationFromRestriction_add_le
-- name    : SNumbers.deviationFromRestriction_add_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:02:07.482931+00:00
-- url     : https://prove2.me/theorems/d5bb81dc-c05c-4056-8fa5-76fe58d3bcd6
-- title:
--   SNumbers: deviation From Restriction add le
-- statement:
--   The triangle inequality for restrictions: `‖(S + T)|_M‖ ≤ ‖S|_M‖ + ‖T|_M‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L249-L254
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L249-L254

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

theorem SNumbers.deviationFromRestriction_add_le (S T : X →L[𝕜] Y) (M : Submodule 𝕜 X) :
    deviationFromRestriction (S + T) M ≤
      deviationFromRestriction S M + deviationFromRestriction T M := by sorry
