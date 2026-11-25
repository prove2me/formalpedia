-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_term_eq_b68ba4cef9fc
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_term_eq_b68ba4cef9fc
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:10:04.849308+00:00
-- url     : https://prove2.me/theorems/cba88b33-fcdd-40a7-8a87-92cad5b2a729
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR divided Difference Expansion term eq b68ba4cef9fc: P2 M Ground Theory Heights  Heights Numbers DVR divided Difference Expansion term eq b68ba4cef9fc
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR divided Difference Expansion term eq b68ba4cef9fc construction uses the P2 M Ground Theory Heights  Heights Numbers DVR divided Difference Expansion term eq b68ba4cef9fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinDivDiffExpansion.lean#L43-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinDivDiffExpansion.lean#L43-L76

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_term_eq_b68ba4cef9fc {r : ℕ} (μ : Fin r →₀ ℕ) (l : Fin r) :
    (X (Sum.inl l) - X (Sum.inr l) : MvPolynomial (Fin r ⊕ Fin r) ℤ) *
      ((∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j) *
        (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) *
        ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j) =
      stair μ l - stair μ (l + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«dividedDifferenceExpansion».«term_eq» := P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_term_eq_b68ba4cef9fc
