-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_weight_blockWeight_apply_6df27136a502
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_weight_blockWeight_apply_6df27136a502
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:12:40.456041+00:00
-- url     : https://prove2.me/theorems/52e2cfd4-2a3a-414d-afc1-70d5d342e553
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR weight block Weight apply 6df27136a502: P2 M Ground Theory Heights  Heights Numbers DVR weight block Weight apply 6df27136a502
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR weight block Weight apply 6df27136a502 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR weight block Weight apply 6df27136a502 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PVocabMultiHomog.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PVocabMultiHomog.lean#L13-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomog
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
open MvPolynomial
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_weight_blockWeight_apply_6df27136a502 {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blockWeight ι) m k = ∑ i, m ⟨k, i⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«weight_blockWeight_apply» := P2M_GroundTheory_Heights__Heights_NumbersDVR_weight_blockWeight_apply_6df27136a502
