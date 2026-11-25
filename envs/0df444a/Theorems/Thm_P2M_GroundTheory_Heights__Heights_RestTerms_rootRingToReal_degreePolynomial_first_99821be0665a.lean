-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_degreePolynomial_first_99821be0665a
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_degreePolynomial_first_99821be0665a
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:36:06.799573+00:00
-- url     : https://prove2.me/theorems/34d71a4d-d491-4af0-9f61-028c892ac02e
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real degree Polynomial first 99821be0665a: P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real degree Polynomial first 99821be0
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real degree Polynomial first 99821be0665a construction uses the P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real degree Polynomial first 99821be0665a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L155-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L155-L160

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_degreePolynomial_first_99821be0665a (f r a : ℕ) :
    rootRingToReal f (r + a) r a rfl
        (smallBlockMu f r a .first ^ (f * (r * a)) * fibreClass f r a .first) =
      IndefiniteRowSideFullHecke.RestTerms.degPoly f r a false := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«rootRingToReal_degreePolynomial_first» := P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_degreePolynomial_first_99821be0665a
