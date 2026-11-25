-- Prove2me | Theorems.Thm_P2M_SNumbers_L1Linf_summable_norm_sq_row__73d6b93b43be
-- name    : P2M_SNumbers_L1Linf_summable_norm_sq_row__73d6b93b43be
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:14:40.828824+00:00
-- url     : https://prove2.me/theorems/80af9a95-c633-4548-84d7-c758d3f42b18
-- title:
--   P2 M SNumbers L1 Linf summable norm sq row  73d6b93b43be: P2 M SNumbers L1 Linf summable norm sq row  73d6b93b43be
-- statement:
--   The P2 M SNumbers L1 Linf summable norm sq row  73d6b93b43be construction uses the P2 M SNumbers L1 Linf summable norm sq row  73d6b93b43be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L453-L454
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L453-L454

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
variable (A : L2 𝕜 →L[𝕜] L1 𝕜) (B : Linf 𝕜 →L[𝕜] L2 𝕜)

theorem P2M_SNumbers_L1Linf_summable_norm_sq_row__73d6b93b43be : Summable fun j => ‖row A j‖ ^ 2 := by sorry

alias «SNumbers».«L1Linf».«summable_norm_sq_row'» := P2M_SNumbers_L1Linf_summable_norm_sq_row__73d6b93b43be
