-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_expansion_f69d2f136b96
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_expansion_f69d2f136b96
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:10:44.243783+00:00
-- url     : https://prove2.me/theorems/ebedc8f1-6cdf-4bef-b17d-ccf5f645550e
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR exists expansion f69d2f136b96: P2 M Ground Theory Heights  Heights Numbers DVR exists expansion f69d2f136b96
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR exists expansion f69d2f136b96 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR exists expansion f69d2f136b96 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagIndependenceAlgebra.lean#L192-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagIndependenceAlgebra.lean#L192-L215

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_expansion_f69d2f136b96 {n : ℕ} (A : MvPolynomial (Fin n) ℤ) :
    ∃ Gs : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ,
      rename Sum.inl A - rename Sum.inr A = ∑ i, (X (Sum.inl i) - X (Sum.inr i)) * Gs i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«exists_expansion» := P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_expansion_f69d2f136b96
