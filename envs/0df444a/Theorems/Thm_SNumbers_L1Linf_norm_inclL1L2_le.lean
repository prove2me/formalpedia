-- Prove2me | Theorems.Thm_SNumbers_L1Linf_norm_inclL1L2_le
-- name    : SNumbers.L1Linf.norm_inclL1L2_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:27:10.19156+00:00
-- url     : https://prove2.me/theorems/5b9dbdd1-5950-40e2-b3ec-29107de94adf
-- title:
--   L1 Linf: norm incl L1 L2 le
-- statement:
--   The L1 Linf construction uses the norm incl L1 L2 le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L397-L398
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L397-L398

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

theorem SNumbers.L1Linf.norm_inclL1L2_le : ‖(inclL1L2 : L1 𝕜 →L[𝕜] L2 𝕜)‖ ≤ 1 := by sorry
