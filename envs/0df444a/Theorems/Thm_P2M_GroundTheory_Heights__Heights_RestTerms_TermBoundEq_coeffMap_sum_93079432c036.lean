-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_coeffMap_sum_93079432c036
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_coeffMap_sum_93079432c036
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:21:38.044821+00:00
-- url     : https://prove2.me/theorems/f32c0fbd-c290-4476-a490-4b21cef6ad3a
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Term Bound Eq coeff Map sum 93079432c036: P2 M Ground Theory Heights  Heights Rest Terms Term Bound Eq coeff Map sum 93079432c036
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Term Bound Eq coeff Map sum 93079432c036 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Term Bound Eq coeff Map sum 93079432c036 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealRootRingToRealAlt.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealRootRingToRealAlt.lean#L39-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealRootRingToRealAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.TermBoundEq
variable {σ : Type*} (φ : Module.Dual ℚ ℝ)

theorem P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_coeffMap_sum_93079432c036 {ι : Type*} (s : Finset ι) (P : ι → MvPolynomial σ ℝ) :
    coeffMap φ (∑ i ∈ s, P i) = ∑ i ∈ s, coeffMap φ (P i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«TermBoundEq».«coeffMap_sum» := P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_coeffMap_sum_93079432c036
