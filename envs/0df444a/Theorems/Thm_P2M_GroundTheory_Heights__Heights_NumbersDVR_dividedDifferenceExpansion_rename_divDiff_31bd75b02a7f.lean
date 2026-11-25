-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_rename_divDiff_31bd75b02a7f
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_rename_divDiff_31bd75b02a7f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:16:22.106351+00:00
-- url     : https://prove2.me/theorems/99f4e9ea-339a-5fbc-b5db-08b7438f47ba
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR divided Difference Expansion rename div Diff 31bd75b02a7f: P2 M Ground Theory Heights  Heights Numbers DVR divided Difference Expansion rename div Diff
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR divided Difference Expansion rename div Diff 31bd75b02a7f construction uses the P2 M Ground Theory Heights  Heights Numbers DVR divided Difference Expansion rename div Diff 31bd75b02a7f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinDivDiffExpansion.lean#L96-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinDivDiffExpansion.lean#L96-L106

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_rename_divDiff_31bd75b02a7f {r : ℕ} (l : Fin r) (G : MvPolynomial (Fin r) ℤ) :
    rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l G) =
      ∑ μ ∈ G.support, C (G.coeff μ) *
        ((∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j) *
          (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) *
          ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«dividedDifferenceExpansion».«rename_divDiff» := P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_rename_divDiff_31bd75b02a7f
