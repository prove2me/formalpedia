-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_encard_biUnion_finset_le_8a3bd962f7b6
-- name    : P2M_GroundTheory_Heights__Heights_encard_biUnion_finset_le_8a3bd962f7b6
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:45:56.502407+00:00
-- url     : https://prove2.me/theorems/01f89f27-3bd4-4604-8501-122b04961b10
-- title:
--   P2 M Ground Theory Heights  Heights encard bi Union finset le 8a3bd962f7b6: P2 M Ground Theory Heights  Heights encard bi Union finset le 8a3bd962f7b6
-- statement:
--   The P2 M Ground Theory Heights  Heights encard bi Union finset le 8a3bd962f7b6 construction uses the P2 M Ground Theory Heights  Heights encard bi Union finset le 8a3bd962f7b6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedPointsCount.lean#L24-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedPointsCount.lean#L24-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedPointsCountPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIsolatedPointsCount
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
open MvPolynomial Topology ComplexSets
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_encard_biUnion_finset_le_8a3bd962f7b6 {ι α : Type*} (S : Finset ι) (f : ι → Set α) :
    (⋃ i ∈ S, f i).encard ≤ ∑ i ∈ S, (f i).encard := by sorry

alias «GroundTheory».«Heights₂».«Heights».«encard_biUnion_finset_le» := P2M_GroundTheory_Heights__Heights_encard_biUnion_finset_le_8a3bd962f7b6
