-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_restPolynomial_last_02bc100292b7
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_restPolynomial_last_02bc100292b7
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:36:32.713403+00:00
-- url     : https://prove2.me/theorems/d51edc13-f432-441c-8839-12de7a698279
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real rest Polynomial last 02bc100292b7: P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real rest Polynomial last 02bc100292b7
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real rest Polynomial last 02bc100292b7 construction uses the P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real rest Polynomial last 02bc100292b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L136-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L136-L140

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_restPolynomial_last_02bc100292b7 (f r a : ℕ) :
    rootRingToReal f (r + a) a r (Nat.add_comm r a) (restPolynomial f r a .last) =
      IndefiniteRowSideFullHecke.RestTerms.restPoly f a r true := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«rootRingToReal_restPolynomial_last» := P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_restPolynomial_last_02bc100292b7
