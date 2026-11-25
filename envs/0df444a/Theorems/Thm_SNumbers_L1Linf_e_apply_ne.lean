-- Prove2me | Theorems.Thm_SNumbers_L1Linf_e_apply_ne
-- name    : SNumbers.L1Linf.e_apply_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:13:06.161069+00:00
-- url     : https://prove2.me/theorems/a43b8ca6-bd2f-4f4c-8b4b-8dc163706034
-- title:
--   L1 Linf: e apply ne
-- statement:
--   The L1 Linf construction uses the e apply ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L95-L96
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L95-L96

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

theorem SNumbers.L1Linf.e_apply_ne {i j : ℕ} (h : j ≠ i) : (e i : L1 𝕜) j = 0 := by sorry
