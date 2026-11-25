-- Prove2me | Theorems.Thm_SNumbers_L1Linf_norm_emb1_apply_le
-- name    : SNumbers.L1Linf.norm_emb1_apply_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:13:49.03394+00:00
-- url     : https://prove2.me/theorems/f7a83495-6c76-472d-bb5a-e14e20e01aef
-- title:
--   L1 Linf: norm emb1 apply le
-- statement:
--   The L1 Linf construction uses the norm emb1 apply le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L234-L243
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L234-L243

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

theorem SNumbers.L1Linf.norm_emb1_apply_le (m : ℕ) (v : EuclideanSpace 𝕜 (Fin m)) :
    ‖emb1 m v‖ ≤ Real.sqrt m * ‖v‖ := by sorry
