-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_PrimeOpensCover_not_mem_of_isCoprime_27a59e8a7789
-- name    : P2M_GroundTheory_Heights__Heights_Model_PrimeOpensCover_not_mem_of_isCoprime_27a59e8a7789
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:39:32.717108+00:00
-- url     : https://prove2.me/theorems/6340b572-5f50-5460-8b15-10c608cb6aaa
-- title:
--   P2 M Ground Theory Heights  Heights Model Prime Opens Cover not mem of is Coprime 27a59e8a7789: P2 M Ground Theory Heights  Heights Model Prime Opens Cover not mem of is Coprime 27a59e8a7789
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Prime Opens Cover not mem of is Coprime 27a59e8a7789 construction uses the P2 M Ground Theory Heights  Heights Model Prime Opens Cover not mem of is Coprime 27a59e8a7789 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PPrimeOpensCover.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PPrimeOpensCover.lean#L11-L15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PPrimeOpensCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open AlgebraicGeometry TopologicalSpace
open GroundTheory.Heights₂.Heights.Model.PrimeOpensCover

theorem P2M_GroundTheory_Heights__Heights_Model_PrimeOpensCover_not_mem_of_isCoprime_27a59e8a7789 {P : Ideal ℤ} (hP : P ≠ ⊤) {a b : ℤ} (h : IsCoprime a b)
    (ha : a ∈ P) : b ∉ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«PrimeOpensCover».«not_mem_of_isCoprime» := P2M_GroundTheory_Heights__Heights_Model_PrimeOpensCover_not_mem_of_isCoprime_27a59e8a7789
