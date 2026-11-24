-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_coeff_coeffMap_90caddac2fb8
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_coeff_coeffMap_90caddac2fb8
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:00:39.62219+00:00
-- url     : https://prove2.me/theorems/11afb909-e540-4420-9ef2-e6efeb87935f
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Term Bound Eq coeff coeff Map 90caddac2fb8: P2 M Ground Theory Heights  Heights Rest Terms Term Bound Eq coeff coeff Map 90caddac2fb8
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Term Bound Eq coeff coeff Map 90caddac2fb8 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Term Bound Eq coeff coeff Map 90caddac2fb8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealRootRingToRealAlt.lean#L29-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealRootRingToRealAlt.lean#L29-L37

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_coeff_coeffMap_90caddac2fb8 (P : MvPolynomial σ ℝ) (d : σ →₀ ℕ) :
    coeff d (coeffMap φ P) = φ (coeff d P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«TermBoundEq».«coeff_coeffMap» := P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_coeff_coeffMap_90caddac2fb8
