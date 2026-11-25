-- Prove2me | Theorems.Thm_SNumbers_L1Linf_incl_apply
-- name    : SNumbers.L1Linf.incl_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:40:27.057985+00:00
-- url     : https://prove2.me/theorems/c9da1ea4-072f-50c8-936a-d7c4e3d24633
-- title:
--   L1 Linf: incl apply
-- statement:
--   The L1 Linf construction uses the incl apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L81-L82
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L81-L82

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

theorem SNumbers.L1Linf.incl_apply (f : L1 𝕜) (i : ℕ) :
    ((incl : L1 𝕜 →L[𝕜] Linf 𝕜) f) i = f i := by sorry

attribute [defeq] SNumbers.L1Linf.incl_apply
