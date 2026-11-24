-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_X_6be993a34174
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_X_6be993a34174
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:44.796421+00:00
-- url     : https://prove2.me/theorems/37baef19-3a60-4211-8e0e-fab1ff2bad6c
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real X 6be993a34174: P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real X 6be993a34174
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real X 6be993a34174 construction uses the P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real X 6be993a34174 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L16-L19

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_X_6be993a34174 (f N j k : ℕ) (h : N = j + k) (v : Fin f × Fin N) :
    rootRingToReal f N j k h (X v) = X (v.1, finCongr h v.2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«rootRingToReal_X» := P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_X_6be993a34174
