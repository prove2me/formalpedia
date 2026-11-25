-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_koszul_finset_1a72aab2fcc7
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_koszul_finset_1a72aab2fcc7
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:07:14.621746+00:00
-- url     : https://prove2.me/theorems/44df8cdf-5f92-4e33-9ef7-19345a525baf
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR koszul finset 1a72aab2fcc7: P2 M Ground Theory Heights  Heights Numbers DVR koszul finset 1a72aab2fcc7
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR koszul finset 1a72aab2fcc7 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR koszul finset 1a72aab2fcc7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L94-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L94-L166

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMixedDiffLinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OfSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberExpansionKoszul
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
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_koszul_finset_1a72aab2fcc7 (s : Finset (Fin n)) :
    ∀ G : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ, (∀ i, i ∉ s → G i = 0) →
      ∑ i, pairDiff i * G i = 0 →
      ∃ K : Fin n → Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ,
        (∀ i j, K i j = -K j i) ∧ ∀ i, G i = ∑ j, pairDiff j * K i j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«koszul_finset» := P2M_GroundTheory_Heights__Heights_NumbersDVR_koszul_finset_1a72aab2fcc7
