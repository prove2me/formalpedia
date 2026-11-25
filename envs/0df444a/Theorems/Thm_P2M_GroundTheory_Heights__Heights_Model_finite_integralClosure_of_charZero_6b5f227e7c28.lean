-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_finite_integralClosure_of_charZero_6b5f227e7c28
-- name    : P2M_GroundTheory_Heights__Heights_Model_finite_integralClosure_of_charZero_6b5f227e7c28
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:24.695981+00:00
-- url     : https://prove2.me/theorems/1aa7818a-1c43-4d09-9816-a1ee703241e8
-- title:
--   P2 M Ground Theory Heights  Heights Model finite integral Closure of char Zero 6b5f227e7c28: P2 M Ground Theory Heights  Heights Model finite integral Closure of char Zero 6b5f227e7c28
-- statement:
--   The P2 M Ground Theory Heights  Heights Model finite integral Closure of char Zero 6b5f227e7c28 construction uses the P2 M Ground Theory Heights  Heights Model finite integral Closure of char Zero 6b5f227e7c28 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteIntegralClosureCharZero.lean#L166-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteIntegralClosureCharZero.lean#L166-L191

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureCharZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open scoped nonZeroDivisors
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model

theorem P2M_GroundTheory_Heights__Heights_Model_finite_integralClosure_of_charZero_6b5f227e7c28
    (A : Type*) [CommRing A] [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A K L] :
    Module.Finite A (integralClosure A L) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«finite_integralClosure_of_charZero» := P2M_GroundTheory_Heights__Heights_Model_finite_integralClosure_of_charZero_6b5f227e7c28
