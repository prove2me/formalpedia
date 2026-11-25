-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_degreePolynomial_last_c5eb8f957917
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_degreePolynomial_last_c5eb8f957917
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:37:18.738627+00:00
-- url     : https://prove2.me/theorems/9ce49606-33ac-4e0c-8fa5-97dd297b933e
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real degree Polynomial last c5eb8f957917: P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real degree Polynomial last c5eb8f9579
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real degree Polynomial last c5eb8f957917 construction uses the P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real degree Polynomial last c5eb8f957917 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L148-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L148-L153

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_degreePolynomial_last_c5eb8f957917 (f r a : ℕ) :
    rootRingToReal f (r + a) a r (Nat.add_comm r a)
        (smallBlockMu f r a .last ^ (f * (r * a)) * fibreClass f r a .last) =
      IndefiniteRowSideFullHecke.RestTerms.degPoly f a r true := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«rootRingToReal_degreePolynomial_last» := P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_degreePolynomial_last_c5eb8f957917
