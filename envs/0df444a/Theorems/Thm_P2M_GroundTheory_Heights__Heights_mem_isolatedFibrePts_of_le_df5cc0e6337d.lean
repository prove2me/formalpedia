-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_isolatedFibrePts_of_le_df5cc0e6337d
-- name    : P2M_GroundTheory_Heights__Heights_mem_isolatedFibrePts_of_le_df5cc0e6337d
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:49:17.379639+00:00
-- url     : https://prove2.me/theorems/9d69dc4c-4e13-4b37-bfb6-bc492007778b
-- title:
--   P2 M Ground Theory Heights  Heights mem isolated Fibre Pts of le df5cc0e6337d: P2 M Ground Theory Heights  Heights mem isolated Fibre Pts of le df5cc0e6337d
-- statement:
--   The P2 M Ground Theory Heights  Heights mem isolated Fibre Pts of le df5cc0e6337d construction uses the P2 M Ground Theory Heights  Heights mem isolated Fibre Pts of le df5cc0e6337d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedPointsCount.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedPointsCount.lean#L18-L22

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

theorem P2M_GroundTheory_Heights__Heights_mem_isolatedFibrePts_of_le_df5cc0e6337d {n m : ℕ} {J P : Ideal (MvPolynomial (Fin n) ℂ)} (hJP : J ≤ P)
    (Q : Fin m → MvPolynomial (Fin n) ℂ) (z : Fin m → ℂ) {x : Fin n → ℂ}
    (hx : x ∈ isolatedFibrePts J Q z) (hxP : x ∈ zeroSet P) : x ∈ isolatedFibrePts P Q z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_isolatedFibrePts_of_le» := P2M_GroundTheory_Heights__Heights_mem_isolatedFibrePts_of_le_df5cc0e6337d
