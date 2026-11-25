-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_isHomogeneous_iff_1053195a886d
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_isHomogeneous_iff_1053195a886d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:36:58.746576+00:00
-- url     : https://prove2.me/theorems/057bfd21-7626-56c3-ae30-5c3251b80931
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real is Homogeneous iff 1053195a886d: P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real is Homogeneous iff 1053195a886d
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real is Homogeneous iff 1053195a886d construction uses the P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real is Homogeneous iff 1053195a886d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L25-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L25-L36

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_isHomogeneous_iff_1053195a886d (f N j k : ℕ) (h : N = j + k) (P : RootRing f N) (n : ℕ) :
    (rootRingToReal f N j k h P).IsHomogeneous n ↔ P.IsHomogeneous n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«rootRingToReal_isHomogeneous_iff» := P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_isHomogeneous_iff_1053195a886d
