-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_coeffMap_map_mul_301e0e18d5cf
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_coeffMap_map_mul_301e0e18d5cf
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:21:17.496153+00:00
-- url     : https://prove2.me/theorems/543390a3-971c-4ff6-909f-0e0613dd53f0
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Term Bound Eq coeff Map map mul 301e0e18d5cf: P2 M Ground Theory Heights  Heights Rest Terms Term Bound Eq coeff Map map mul 301e0e18d5cf
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Term Bound Eq coeff Map map mul 301e0e18d5cf construction uses the P2 M Ground Theory Heights  Heights Rest Terms Term Bound Eq coeff Map map mul 301e0e18d5cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealRootRingToRealAlt.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealRootRingToRealAlt.lean#L44-L50

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_coeffMap_map_mul_301e0e18d5cf (R : MvPolynomial σ ℚ) (P : MvPolynomial σ ℝ) :
    coeffMap φ (map (algebraMap ℚ ℝ) R * P) = R * coeffMap φ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«TermBoundEq».«coeffMap_map_mul» := P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_coeffMap_map_mul_301e0e18d5cf
