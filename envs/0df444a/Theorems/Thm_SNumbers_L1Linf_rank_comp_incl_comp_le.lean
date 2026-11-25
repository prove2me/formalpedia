-- Prove2me | Theorems.Thm_SNumbers_L1Linf_rank_comp_incl_comp_le
-- name    : SNumbers.L1Linf.rank_comp_incl_comp_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:15:50.72747+00:00
-- url     : https://prove2.me/theorems/9251fe8d-7262-43a2-b69d-39c851b37637
-- title:
--   L1 Linf: rank comp incl comp le
-- statement:
--   `B I A` has at most the rank of `A`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L503-L510
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L503-L510

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

theorem SNumbers.L1Linf.rank_comp_incl_comp_le :
    (B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp A)).rank ≤ A.rank := by sorry
