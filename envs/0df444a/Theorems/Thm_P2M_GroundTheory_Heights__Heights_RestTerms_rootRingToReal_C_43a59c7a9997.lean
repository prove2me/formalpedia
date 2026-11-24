-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_C_43a59c7a9997
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_C_43a59c7a9997
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:42.112502+00:00
-- url     : https://prove2.me/theorems/34e7235e-7f99-41bb-8a3c-1c14920a04e0
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real C 43a59c7a9997: P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real C 43a59c7a9997
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real C 43a59c7a9997 construction uses the P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real C 43a59c7a9997 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L21-L23

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_C_43a59c7a9997 (f N j k : ℕ) (h : N = j + k) (q : ℚ) :
    rootRingToReal f N j k h (C q) = C (q : ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«rootRingToReal_C» := P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_C_43a59c7a9997
