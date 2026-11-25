-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineDegreeProof_weight_blockWeight_apply_2427db235b67
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineDegreeProof_weight_blockWeight_apply_2427db235b67
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:29:59.596435+00:00
-- url     : https://prove2.me/theorems/34db0adc-d685-415a-a503-b8f2caf7736d
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Degree Proof weight block Weight apply 2427db235b67: P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Degree Proof weight block Weigh
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Degree Proof weight block Weight apply 2427db235b67 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Degree Proof weight block Weight apply 2427db235b67 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineDegree.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineDegree.lean#L14-L19

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineDegreeProof_weight_blockWeight_apply_2427db235b67 {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*}
    [∀ k, Fintype (ι k)] (μ : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blockWeight ι) μ k = ∑ i : ι k, μ ⟨k, i⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagLineDegreeProof».«weight_blockWeight_apply» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineDegreeProof_weight_blockWeight_apply_2427db235b67
