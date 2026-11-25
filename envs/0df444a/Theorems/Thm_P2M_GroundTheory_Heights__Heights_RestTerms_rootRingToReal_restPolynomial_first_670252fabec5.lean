-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_restPolynomial_first_670252fabec5
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_restPolynomial_first_670252fabec5
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:36:44.378803+00:00
-- url     : https://prove2.me/theorems/19986c41-4380-4dcf-b38a-90d965ec6226
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real rest Polynomial first 670252fabec5: P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real rest Polynomial first 670252fabec5
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real rest Polynomial first 670252fabec5 construction uses the P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real rest Polynomial first 670252fabec5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L142-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L142-L146

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_restPolynomial_first_670252fabec5 (f r a : ℕ) :
    rootRingToReal f (r + a) r a rfl (restPolynomial f r a .first) =
      IndefiniteRowSideFullHecke.RestTerms.restPoly f r a false := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«rootRingToReal_restPolynomial_first» := P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_restPolynomial_first_670252fabec5
