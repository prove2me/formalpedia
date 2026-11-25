-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_PrimeOpensCover_mem_of_dvd_mem_67dc305db825
-- name    : P2M_GroundTheory_Heights__Heights_Model_PrimeOpensCover_mem_of_dvd_mem_67dc305db825
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:30:06.876503+00:00
-- url     : https://prove2.me/theorems/16eb41d3-70be-49d5-bccb-3114b1499094
-- title:
--   P2 M Ground Theory Heights  Heights Model Prime Opens Cover mem of dvd mem 67dc305db825: P2 M Ground Theory Heights  Heights Model Prime Opens Cover mem of dvd mem 67dc305db825
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Prime Opens Cover mem of dvd mem 67dc305db825 construction uses the P2 M Ground Theory Heights  Heights Model Prime Opens Cover mem of dvd mem 67dc305db825 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PPrimeOpensCover.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PPrimeOpensCover.lean#L17-L19

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

theorem P2M_GroundTheory_Heights__Heights_Model_PrimeOpensCover_mem_of_dvd_mem_67dc305db825 {P : Ideal ℤ} {a b : ℤ} (h : a ∣ b) (ha : a ∈ P) : b ∈ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«PrimeOpensCover».«mem_of_dvd_mem» := P2M_GroundTheory_Heights__Heights_Model_PrimeOpensCover_mem_of_dvd_mem_67dc305db825
