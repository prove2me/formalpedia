-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_blockPowerSum_8334d045ed2f
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_blockPowerSum_8334d045ed2f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:33:34.462147+00:00
-- url     : https://prove2.me/theorems/a30164fd-f806-407c-8729-ee56505d6830
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real block Power Sum 8334d045ed2f: P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real block Power Sum 8334d045ed2f
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real block Power Sum 8334d045ed2f construction uses the P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real block Power Sum 8334d045ed2f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L71-L74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHomogeneousComponentMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_blockPowerSum_8334d045ed2f (f N j k : ℕ) (h : N = j + k) (m : ℕ) (τ : Fin f) :
    rootRingToReal f N j k h (blockPowerSum f N m τ) = IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«rootRingToReal_blockPowerSum» := P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_blockPowerSum_8334d045ed2f
