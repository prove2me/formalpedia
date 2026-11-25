-- Prove2me | Theorems.Thm_SNumbers_deviationFromRestriction_mono
-- name    : SNumbers.deviationFromRestriction_mono
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:02:04.922892+00:00
-- url     : https://prove2.me/theorems/f9b5a15f-f751-4773-996a-d0f649c767bd
-- title:
--   SNumbers: deviation From Restriction mono
-- statement:
--   Restricting to a smaller subspace does not increase the norm:
--   `M' ≤ M ⇒ ‖S|_{M'}‖ ≤ ‖S|_M‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L242-L246
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L242-L246

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

theorem SNumbers.deviationFromRestriction_mono (S : X →L[𝕜] Y) {M M' : Submodule 𝕜 X} (h : M' ≤ M) :
    deviationFromRestriction S M' ≤ deviationFromRestriction S M := by sorry
