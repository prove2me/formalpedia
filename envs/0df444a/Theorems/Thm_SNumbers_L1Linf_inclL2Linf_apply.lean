-- Prove2me | Theorems.Thm_SNumbers_L1Linf_inclL2Linf_apply
-- name    : SNumbers.L1Linf.inclL2Linf_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:41:02.1795+00:00
-- url     : https://prove2.me/theorems/1f5048cd-c4e5-58f2-9536-86fb6e860e93
-- title:
--   L1 Linf: incl L2 Linf apply
-- statement:
--   The L1 Linf construction uses the incl L2 Linf apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L405-L406
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L405-L406

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

theorem SNumbers.L1Linf.inclL2Linf_apply (f : L2 𝕜) (i : ℕ) :
    ((inclL2Linf : L2 𝕜 →L[𝕜] Linf 𝕜) f) i = f i := by sorry

attribute [defeq] SNumbers.L1Linf.inclL2Linf_apply
