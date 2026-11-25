-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineDegreeProof_chart_form_792b75e5fddd
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineDegreeProof_chart_form_792b75e5fddd
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:27.326274+00:00
-- url     : https://prove2.me/theorems/cafbf4e9-2971-4486-be22-8c20a300450c
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Degree Proof chart form 792b75e5fddd: P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Degree Proof chart form 792b75e5fddd
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Degree Proof chart form 792b75e5fddd construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Degree Proof chart form 792b75e5fddd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineDegree.lean#L48-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineDegree.lean#L48-L87

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagLineDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSplitRelDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagLineDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineDegreeProof

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineDegreeProof_chart_form_792b75e5fddd {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {F Ω : Type*} [Field F]
    [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : segreVec y c ≠ 0) {α : Ω}
    (hα : α ∈ chartRing F (segreVec y) c) :
    ∃ (m : ℕ) (A : MRing ι F), IsMultiHomog A (fun _ => m) ∧ α * segreVec y c ^ m = aeval y A := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagLineDegreeProof».«chart_form» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineDegreeProof_chart_form_792b75e5fddd
