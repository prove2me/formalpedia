-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_smallPowerSum_last_07f068e6fede
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_smallPowerSum_last_07f068e6fede
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:38:51.753424+00:00
-- url     : https://prove2.me/theorems/d88ae038-a766-44c5-a218-54c47546278a
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real small Power Sum last 07f068e6fede: P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real small Power Sum last 07f068e6fede
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real small Power Sum last 07f068e6fede construction uses the P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real small Power Sum last 07f068e6fede property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L76-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L76-L82

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_smallPowerSum_last_07f068e6fede (f r a m : ℕ) (τ : Fin f) :
    rootRingToReal f (r + a) a r (Nat.add_comm r a) (smallPowerSum f r a .last m τ) =
      IndefiniteRowSideFullHecke.RestTerms.smallPsum f a r true m τ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«rootRingToReal_smallPowerSum_last» := P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_smallPowerSum_last_07f068e6fede
