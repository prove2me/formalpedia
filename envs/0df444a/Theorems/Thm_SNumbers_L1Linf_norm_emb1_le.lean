-- Prove2me | Theorems.Thm_SNumbers_L1Linf_norm_emb1_le
-- name    : SNumbers.L1Linf.norm_emb1_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:14:05.814229+00:00
-- url     : https://prove2.me/theorems/35a641e6-fba2-4cc0-954f-1df0395fe8c7
-- title:
--   L1 Linf: norm emb1 le
-- statement:
--   The L1 Linf construction uses the norm emb1 le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L245-L246
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L245-L246

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

theorem SNumbers.L1Linf.norm_emb1_le (m : ℕ) : ‖(emb1 m : EuclideanSpace 𝕜 (Fin m) →L[𝕜] L1 𝕜)‖ ≤ Real.sqrt m := by sorry
