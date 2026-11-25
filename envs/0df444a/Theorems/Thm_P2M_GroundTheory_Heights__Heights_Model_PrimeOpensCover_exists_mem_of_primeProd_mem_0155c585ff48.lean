-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_PrimeOpensCover_exists_mem_of_primeProd_mem_0155c585ff48
-- name    : P2M_GroundTheory_Heights__Heights_Model_PrimeOpensCover_exists_mem_of_primeProd_mem_0155c585ff48
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:31.672183+00:00
-- url     : https://prove2.me/theorems/8a2e4ec9-d162-4716-9d2a-174da8c772e3
-- title:
--   P2 M Ground Theory Heights  Heights Model Prime Opens Cover exists mem of prime Prod mem 0155c585ff48: P2 M Ground Theory Heights  Heights Model Prime Opens Cover exists mem of prime Prod mem 0155c585
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Prime Opens Cover exists mem of prime Prod mem 0155c585ff48 construction uses the P2 M Ground Theory Heights  Heights Model Prime Opens Cover exists mem of prime Prod mem 0155c585ff48 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PPrimeOpensCover.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PPrimeOpensCover.lean#L21-L23

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

theorem P2M_GroundTheory_Heights__Heights_Model_PrimeOpensCover_exists_mem_of_primeProd_mem_0155c585ff48 {P : Ideal ℤ} [P.IsPrime] {S : Finset Nat.Primes}
    (h : primeProd S ∈ P) : ∃ r ∈ S, ((r : ℕ) : ℤ) ∈ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«PrimeOpensCover».«exists_mem_of_primeProd_mem» := P2M_GroundTheory_Heights__Heights_Model_PrimeOpensCover_exists_mem_of_primeProd_mem_0155c585ff48
