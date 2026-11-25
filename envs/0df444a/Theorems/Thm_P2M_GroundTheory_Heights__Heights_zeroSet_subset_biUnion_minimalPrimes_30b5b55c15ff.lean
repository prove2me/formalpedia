-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_zeroSet_subset_biUnion_minimalPrimes_30b5b55c15ff
-- name    : P2M_GroundTheory_Heights__Heights_zeroSet_subset_biUnion_minimalPrimes_30b5b55c15ff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:51:37.401209+00:00
-- url     : https://prove2.me/theorems/2b377dda-d079-4166-884c-edfe3fcc587b
-- title:
--   P2 M Ground Theory Heights  Heights zero Set subset bi Union minimal Primes 30b5b55c15ff: P2 M Ground Theory Heights  Heights zero Set subset bi Union minimal Primes 30b5b55c15ff
-- statement:
--   The P2 M Ground Theory Heights  Heights zero Set subset bi Union minimal Primes 30b5b55c15ff construction uses the P2 M Ground Theory Heights  Heights zero Set subset bi Union minimal Primes 30b5b55c15ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSmallSetTubeVolume.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSmallSetTubeVolume.lean#L12-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSmallSetTubeVolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeTubeVolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSmallSetTubeVolume
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory ComplexSets
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_zeroSet_subset_biUnion_minimalPrimes_30b5b55c15ff {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    zeroSet I ⊆ ⋃ P ∈ I.minimalPrimes, zeroSet P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«zeroSet_subset_biUnion_minimalPrimes» := P2M_GroundTheory_Heights__Heights_zeroSet_subset_biUnion_minimalPrimes_30b5b55c15ff
