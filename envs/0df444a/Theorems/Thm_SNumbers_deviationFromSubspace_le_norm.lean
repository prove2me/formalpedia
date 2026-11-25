-- Prove2me | Theorems.Thm_SNumbers_deviationFromSubspace_le_norm
-- name    : SNumbers.deviationFromSubspace_le_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:31:18.152639+00:00
-- url     : https://prove2.me/theorems/0c53c237-ab46-49c0-9a90-d2ccddd201fd
-- title:
--   SNumbers: deviation From Subspace le norm
-- statement:
--   The SNumbers construction uses the deviation From Subspace le norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L110-L116
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L110-L116

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

theorem SNumbers.deviationFromSubspace_le_norm (S : X →L[𝕜] Y) (V : Submodule 𝕜 Y) :
    deviationFromSubspace S V ≤ ‖S‖ := by sorry
