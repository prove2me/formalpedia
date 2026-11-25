-- Prove2me | Theorems.Thm_SNumbers_deviationFromSubspace_anti
-- name    : SNumbers.deviationFromSubspace_anti
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:28:06.450877+00:00
-- url     : https://prove2.me/theorems/d73ba04b-c511-4705-a69f-466beb6c8d85
-- title:
--   SNumbers: deviation From Subspace anti
-- statement:
--   Enlarging the subspace does not increase the quotient norm:
--   `V ≤ V' ⇒ ‖π_{V'} ∘ S‖ ≤ ‖π_V ∘ S‖`, since `π_{V'}` factors through `π_V` with a
--   contraction.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L251-L269
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L251-L269

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_QuotientMapNorms
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Kolmogorov
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

theorem SNumbers.deviationFromSubspace_anti (S : X →L[𝕜] Y) {V V' : Submodule 𝕜 Y} (h : V ≤ V') :
    deviationFromSubspace S V' ≤ deviationFromSubspace S V := by sorry
