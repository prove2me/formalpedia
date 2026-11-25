-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_minimalPrime_mem_zeroSet_eb01412e6298
-- name    : P2M_GroundTheory_Heights__Heights_exists_minimalPrime_mem_zeroSet_eb01412e6298
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:46:41.560933+00:00
-- url     : https://prove2.me/theorems/d2cdf252-1ac6-49cf-b0f0-ccd406a355e0
-- title:
--   P2 M Ground Theory Heights  Heights exists minimal Prime mem zero Set eb01412e6298: P2 M Ground Theory Heights  Heights exists minimal Prime mem zero Set eb01412e6298
-- statement:
--   The P2 M Ground Theory Heights  Heights exists minimal Prime mem zero Set eb01412e6298 construction uses the P2 M Ground Theory Heights  Heights exists minimal Prime mem zero Set eb01412e6298 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedPointsCount.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedPointsCount.lean#L11-L16

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

theorem P2M_GroundTheory_Heights__Heights_exists_minimalPrime_mem_zeroSet_eb01412e6298 {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) {x : Fin n → ℂ}
    (hx : x ∈ zeroSet J) : ∃ P ∈ J.minimalPrimes, x ∈ zeroSet P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_minimalPrime_mem_zeroSet» := P2M_GroundTheory_Heights__Heights_exists_minimalPrime_mem_zeroSet_eb01412e6298
