-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_le_of_minimalPrimes_1b7b2c331aa3
-- name    : P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_le_of_minimalPrimes_1b7b2c331aa3
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:18:16.009676+00:00
-- url     : https://prove2.me/theorems/f15f6108-1eed-5939-822c-bc85f678aa0d
-- title:
--   P2 M Ground Theory Heights  Heights ring Krull Dim quotient le of minimal Primes 1b7b2c331aa3: P2 M Ground Theory Heights  Heights ring Krull Dim quotient le of minimal Primes 1b7b2c331aa3
-- statement:
--   The P2 M Ground Theory Heights  Heights ring Krull Dim quotient le of minimal Primes 1b7b2c331aa3 construction uses the P2 M Ground Theory Heights  Heights ring Krull Dim quotient le of minimal Primes 1b7b2c331aa3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PFibreCompDimZ.lean#L11-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PFibreCompDimZ.lean#L11-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsFibreCompDimZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_OfChartPointSecPointSpecChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureCharZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PFibreCompDimZ
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
open MvPolynomial IsDedekindDomain

theorem P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_le_of_minimalPrimes_1b7b2c331aa3 {R : Type*} [CommRing R] (J : Ideal R)
    (k : WithBot ℕ∞) (h : ∀ W ∈ J.minimalPrimes, ringKrullDim (R ⧸ W) ≤ k) :
    ringKrullDim (R ⧸ J) ≤ k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ringKrullDim_quotient_le_of_minimalPrimes» := P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_le_of_minimalPrimes_1b7b2c331aa3
