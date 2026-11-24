-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_fibreClass_last_fe182079683b
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_fibreClass_last_fe182079683b
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:33.323332+00:00
-- url     : https://prove2.me/theorems/558e571f-8294-4dd2-b32c-71fab8276eba
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real fibre Class last fe182079683b: P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real fibre Class last fe182079683b
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real fibre Class last fe182079683b construction uses the P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real fibre Class last fe182079683b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L109-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L109-L120

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_fibreClass_last_fe182079683b (f r a : ℕ) :
    rootRingToReal f (r + a) a r (Nat.add_comm r a) (fibreClass f r a .last) =
      IndefiniteRowSideFullHecke.RestTerms.fibClass f a r true := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«rootRingToReal_fibreClass_last» := P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_fibreClass_last_fe182079683b
