-- Prove2me | Theorems.Thm_SNumbers_L1Linf_norm_projinf_apply_le
-- name    : SNumbers.L1Linf.norm_projinf_apply_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:14:15.938725+00:00
-- url     : https://prove2.me/theorems/d6edfef3-32c9-4199-8480-03c263fd552c
-- title:
--   L1 Linf: norm projinf apply le
-- statement:
--   The L1 Linf construction uses the norm projinf apply le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L266-L282
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L266-L282

module
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_LittleGrothendieck
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_AddOns_Approximable
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Sequences
public import Definitions.Def_SNumbers_Examples_IdentityL1Linfty
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers SNumbers.L1Linf
variable {𝕜 : Type*} [RCLike 𝕜]

theorem SNumbers.L1Linf.norm_projinf_apply_le (m : ℕ) (y : Linf 𝕜) :
    ‖(projinf m : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m)) y‖ ≤ Real.sqrt m * ‖y‖ := by sorry
