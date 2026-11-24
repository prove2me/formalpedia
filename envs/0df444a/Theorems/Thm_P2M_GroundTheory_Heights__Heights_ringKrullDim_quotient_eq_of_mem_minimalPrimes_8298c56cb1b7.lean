-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_eq_of_mem_minimalPrimes_8298c56cb1b7
-- name    : P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_eq_of_mem_minimalPrimes_8298c56cb1b7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:08.690564+00:00
-- url     : https://prove2.me/theorems/1b2b9d91-e6de-4201-9260-16ad7577ffc2
-- title:
--   P2 M Ground Theory Heights  Heights ring Krull Dim quotient eq of mem minimal Primes 8298c56cb1b7: P2 M Ground Theory Heights  Heights ring Krull Dim quotient eq of mem minimal Primes 8298c56cb1b7
-- statement:
--   The P2 M Ground Theory Heights  Heights ring Krull Dim quotient eq of mem minimal Primes 8298c56cb1b7 construction uses the P2 M Ground Theory Heights  Heights ring Krull Dim quotient eq of mem minimal Primes 8298c56cb1b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/CMDepthAssoc.lean#L110-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/CMDepthAssoc.lean#L110-L128

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CMDepthAssoc
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
open IsLocalRing RingTheory.Sequence Pointwise

theorem P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_eq_of_mem_minimalPrimes_8298c56cb1b7 {B : Type*} [CommRing B] [IsCohenMacaulayLocalRing B]
    {P : Ideal B} (hP : P ∈ minimalPrimes B) : ringKrullDim (B ⧸ P) = ringKrullDim B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ringKrullDim_quotient_eq_of_mem_minimalPrimes» := P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_eq_of_mem_minimalPrimes_8298c56cb1b7
