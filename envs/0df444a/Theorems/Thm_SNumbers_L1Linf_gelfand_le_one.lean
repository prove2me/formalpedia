-- Prove2me | Theorems.Thm_SNumbers_L1Linf_gelfand_le_one
-- name    : SNumbers.L1Linf.gelfand_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:26:41.298141+00:00
-- url     : https://prove2.me/theorems/3a233159-bccd-421f-aecb-bea5b7e42e31
-- title:
--   L1 Linf: gelfand le one
-- statement:
--   The L1 Linf construction uses the gelfand le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L104-L106
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L104-L106

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

theorem SNumbers.L1Linf.gelfand_le_one (n : ℕ) :
    gelfandNumber (incl : L1 𝕜 →L[𝕜] Linf 𝕜) n ≤ 1 := by sorry
