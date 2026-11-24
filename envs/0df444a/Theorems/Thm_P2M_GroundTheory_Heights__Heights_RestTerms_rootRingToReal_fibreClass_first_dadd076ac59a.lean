-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_fibreClass_first_dadd076ac59a
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_fibreClass_first_dadd076ac59a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:46.8218+00:00
-- url     : https://prove2.me/theorems/f4eefa54-19c3-4378-8ea9-070b1b0530f4
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real fibre Class first dadd076ac59a: P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real fibre Class first dadd076ac59a
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real fibre Class first dadd076ac59a construction uses the P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real fibre Class first dadd076ac59a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L122-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L122-L134

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_fibreClass_first_dadd076ac59a (f r a : ℕ) :
    rootRingToReal f (r + a) r a rfl (fibreClass f r a .first) =
      IndefiniteRowSideFullHecke.RestTerms.fibClass f r a false := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«rootRingToReal_fibreClass_first» := P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_fibreClass_first_dadd076ac59a
