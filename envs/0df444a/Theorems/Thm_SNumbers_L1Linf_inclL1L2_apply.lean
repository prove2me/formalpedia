-- Prove2me | Theorems.Thm_SNumbers_L1Linf_inclL1L2_apply
-- name    : SNumbers.L1Linf.inclL1L2_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:41:08.072552+00:00
-- url     : https://prove2.me/theorems/7cf5990b-ed78-4662-a5af-3d37e6769bd1
-- title:
--   L1 Linf: incl L1 L2 apply
-- statement:
--   The L1 Linf construction uses the incl L1 L2 apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L394-L395
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L394-L395

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

theorem SNumbers.L1Linf.inclL1L2_apply (f : L1 𝕜) (i : ℕ) :
    ((inclL1L2 : L1 𝕜 →L[𝕜] L2 𝕜) f) i = f i := by sorry

attribute [defeq] SNumbers.L1Linf.inclL1L2_apply
