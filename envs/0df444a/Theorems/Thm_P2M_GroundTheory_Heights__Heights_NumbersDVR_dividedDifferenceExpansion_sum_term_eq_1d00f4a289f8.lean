-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_sum_term_eq_1d00f4a289f8
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_sum_term_eq_1d00f4a289f8
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:18:20.636335+00:00
-- url     : https://prove2.me/theorems/614cb087-0855-543d-9cd5-a34eea765ee9
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR divided Difference Expansion sum term eq 1d00f4a289f8: P2 M Ground Theory Heights  Heights Numbers DVR divided Difference Expansion sum term eq 1d00f4a2
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR divided Difference Expansion sum term eq 1d00f4a289f8 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR divided Difference Expansion sum term eq 1d00f4a289f8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinDivDiffExpansion.lean#L78-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinDivDiffExpansion.lean#L78-L86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinDivDiffExpansion
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
open GroundTheory.Heights₂.Heights.NumbersDVR.dividedDifferenceExpansion

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_sum_term_eq_1d00f4a289f8 {r : ℕ} (μ : Fin r →₀ ℕ) :
    ∑ l : Fin r, (X (Sum.inl l) - X (Sum.inr l) : MvPolynomial (Fin r ⊕ Fin r) ℤ) *
      ((∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j) *
        (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) *
        ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j) =
      ∏ j, X (Sum.inl j) ^ μ j - ∏ j, X (Sum.inr j) ^ μ j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«dividedDifferenceExpansion».«sum_term_eq» := P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_sum_term_eq_1d00f4a289f8
