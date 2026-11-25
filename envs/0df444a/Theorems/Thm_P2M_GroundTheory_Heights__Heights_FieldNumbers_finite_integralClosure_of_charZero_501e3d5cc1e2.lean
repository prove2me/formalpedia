-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_integralClosure_of_charZero_501e3d5cc1e2
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_integralClosure_of_charZero_501e3d5cc1e2
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:11:59.477184+00:00
-- url     : https://prove2.me/theorems/00e00e6c-ffa9-5641-994f-c80e442ffd1e
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers finite integral Closure of char Zero 501e3d5cc1e2: P2 M Ground Theory Heights  Heights Field Numbers finite integral Closure of char Zero 501e3d5cc1e2
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers finite integral Closure of char Zero 501e3d5cc1e2 construction uses the P2 M Ground Theory Heights  Heights Field Numbers finite integral Closure of char Zero 501e3d5cc1e2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/NoetherReduction.lean#L106-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/NoetherReduction.lean#L106-L113

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_NoetherReduction
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
universe u

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_integralClosure_of_charZero_501e3d5cc1e2
    (k A : Type u) [Field k] [CharZero k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A K L] :
    Module.Finite A (integralClosure A L) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«finite_integralClosure_of_charZero» := P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_integralClosure_of_charZero_501e3d5cc1e2
