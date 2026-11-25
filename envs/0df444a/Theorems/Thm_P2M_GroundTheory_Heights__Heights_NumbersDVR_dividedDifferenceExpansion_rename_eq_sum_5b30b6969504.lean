-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_rename_eq_sum_5b30b6969504
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_rename_eq_sum_5b30b6969504
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:10:23.58842+00:00
-- url     : https://prove2.me/theorems/5df8089b-932b-4ae2-99c7-2202c9249386
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR divided Difference Expansion rename eq sum 5b30b6969504: P2 M Ground Theory Heights  Heights Numbers DVR divided Difference Expansion rename eq sum 5b30
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR divided Difference Expansion rename eq sum 5b30b6969504 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR divided Difference Expansion rename eq sum 5b30b6969504 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinDivDiffExpansion.lean#L88-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinDivDiffExpansion.lean#L88-L94

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_rename_eq_sum_5b30b6969504 {r : ℕ} (f : Fin r → Fin r ⊕ Fin r) (G : MvPolynomial (Fin r) ℤ) :
    rename f G = ∑ μ ∈ G.support, C (G.coeff μ) * ∏ j, X (f j) ^ μ j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«dividedDifferenceExpansion».«rename_eq_sum» := P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_rename_eq_sum_5b30b6969504
