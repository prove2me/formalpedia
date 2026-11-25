-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_sum_pairDiff_koszul_778ad1ac75eb
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_sum_pairDiff_koszul_778ad1ac75eb
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:07:34.981542+00:00
-- url     : https://prove2.me/theorems/a83d2356-18f9-4af4-b62f-dc7768774a02
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR sum pair Diff koszul 778ad1ac75eb: P2 M Ground Theory Heights  Heights Numbers DVR sum pair Diff koszul 778ad1ac75eb
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR sum pair Diff koszul 778ad1ac75eb construction uses the P2 M Ground Theory Heights  Heights Numbers DVR sum pair Diff koszul 778ad1ac75eb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L78-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L78-L92

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_sum_pairDiff_koszul_778ad1ac75eb (M : Fin n → Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ)
    (hM : ∀ i j, M i j = -M j i) :
    ∑ i, pairDiff i * ∑ j, pairDiff j * M i j = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«sum_pairDiff_koszul» := P2M_GroundTheory_Heights__Heights_NumbersDVR_sum_pairDiff_koszul_778ad1ac75eb
