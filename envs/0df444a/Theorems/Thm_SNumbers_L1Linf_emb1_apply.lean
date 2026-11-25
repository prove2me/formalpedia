-- Prove2me | Theorems.Thm_SNumbers_L1Linf_emb1_apply
-- name    : SNumbers.L1Linf.emb1_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:42:52.477426+00:00
-- url     : https://prove2.me/theorems/b2b56843-2960-46f3-924a-e74c0db7cebd
-- title:
--   L1 Linf: emb1 apply
-- statement:
--   The L1 Linf construction uses the emb1 apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L229-L232
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L229-L232

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

theorem SNumbers.L1Linf.emb1_apply (m : ℕ) (v : EuclideanSpace 𝕜 (Fin m)) :
    emb1 m v = ∑ i : Fin m, lp.single 1 (i : ℕ) (v i) := by sorry
