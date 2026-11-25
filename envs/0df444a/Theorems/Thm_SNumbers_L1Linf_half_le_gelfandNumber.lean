-- Prove2me | Theorems.Thm_SNumbers_L1Linf_half_le_gelfandNumber
-- name    : SNumbers.L1Linf.half_le_gelfandNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:12:36.980923+00:00
-- url     : https://prove2.me/theorems/7113d1f2-27a8-4579-be4d-30caf72f1db0
-- title:
--   L1 Linf: half le gelfand Number
-- statement:
--   The L1 Linf construction uses the half le gelfand Number property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L115-L202
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L115-L202

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

theorem SNumbers.L1Linf.half_le_gelfandNumber (n : ℕ) :
    (1 : ℝ) / 2 ≤ gelfandNumber (incl : L1 𝕜 →L[𝕜] Linf 𝕜) n := by sorry
