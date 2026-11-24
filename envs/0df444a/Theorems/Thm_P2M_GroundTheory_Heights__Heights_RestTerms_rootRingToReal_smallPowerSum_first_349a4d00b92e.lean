-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_smallPowerSum_first_349a4d00b92e
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_smallPowerSum_first_349a4d00b92e
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:38:18.338471+00:00
-- url     : https://prove2.me/theorems/03ab5f7f-d623-4928-b179-d5b1062a7b2d
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real small Power Sum first 349a4d00b92e: P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real small Power Sum first 349a4d00b92e
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real small Power Sum first 349a4d00b92e construction uses the P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real small Power Sum first 349a4d00b92e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L84-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L84-L91

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_smallPowerSum_first_349a4d00b92e (f r a m : ℕ) (τ : Fin f) :
    rootRingToReal f (r + a) r a rfl (smallPowerSum f r a .first m τ) =
      IndefiniteRowSideFullHecke.RestTerms.smallPsum f r a false m τ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«rootRingToReal_smallPowerSum_first» := P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_smallPowerSum_first_349a4d00b92e
