-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isHomogeneous_of_mem_minimalPrimes_21910d679847
-- name    : P2M_GroundTheory_Heights__Heights_isHomogeneous_of_mem_minimalPrimes_21910d679847
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:47:21.912788+00:00
-- url     : https://prove2.me/theorems/447f1428-9484-4e3e-9c47-b905f26150f9
-- title:
--   P2 M Ground Theory Heights  Heights is Homogeneous of mem minimal Primes 21910d679847: P2 M Ground Theory Heights  Heights is Homogeneous of mem minimal Primes 21910d679847
-- statement:
--   The P2 M Ground Theory Heights  Heights is Homogeneous of mem minimal Primes 21910d679847 construction uses the P2 M Ground Theory Heights  Heights is Homogeneous of mem minimal Primes 21910d679847 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PDivCyclePrime.lean#L24-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PDivCyclePrime.lean#L24-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDivCyclePrime
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
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_isHomogeneous_of_mem_minimalPrimes_21910d679847 {I P : Ideal (MvPolynomial (Fin n) ℂ)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ)) (hP : P ∈ I.minimalPrimes) :
    P.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isHomogeneous_of_mem_minimalPrimes» := P2M_GroundTheory_Heights__Heights_isHomogeneous_of_mem_minimalPrimes_21910d679847
