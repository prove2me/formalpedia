-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_aeval_derivative_minpoly_ne_zero_2c82d18c6b29
-- name    : P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_aeval_derivative_minpoly_ne_zero_2c82d18c6b29
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:43:40.042079+00:00
-- url     : https://prove2.me/theorems/fe52e5b9-fc75-5483-90f8-9b2e9fd0c173
-- title:
--   P2 M Ground Theory Heights  Heights Zero Locus Dim H aeval derivative minpoly ne zero 2c82d18c6b29: P2 M Ground Theory Heights  Heights Zero Locus Dim H aeval derivative minpoly ne zero 2c82d18c6b29
-- statement:
--   The P2 M Ground Theory Heights  Heights Zero Locus Dim H aeval derivative minpoly ne zero 2c82d18c6b29 construction uses the P2 M Ground Theory Heights  Heights Zero Locus Dim H aeval derivative minpoly ne zero 2c82d18c6b29 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ZeroLocusDimHAlg.lean#L28-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ZeroLocusDimHAlg.lean#L28-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ZeroLocusDimHAlg
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
noncomputable section
open GroundTheory.Heights₂.Heights.ZeroLocusDimH

theorem P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_aeval_derivative_minpoly_ne_zero_2c82d18c6b29 {R A : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CharZero R] [CommRing A] [IsDomain A] [Algebra R A]
    [Algebra.IsIntegral R A] (hinj : Function.Injective (algebraMap R A)) (x : A) :
    Polynomial.aeval x (Polynomial.derivative (minpoly R x)) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ZeroLocusDimH».«aeval_derivative_minpoly_ne_zero» := P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_aeval_derivative_minpoly_ne_zero_2c82d18c6b29
