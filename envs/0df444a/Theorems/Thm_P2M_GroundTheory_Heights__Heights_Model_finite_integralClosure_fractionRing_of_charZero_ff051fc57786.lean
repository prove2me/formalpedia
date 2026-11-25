-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_finite_integralClosure_fractionRing_of_charZero_ff051fc57786
-- name    : P2M_GroundTheory_Heights__Heights_Model_finite_integralClosure_fractionRing_of_charZero_ff051fc57786
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:37.371176+00:00
-- url     : https://prove2.me/theorems/c2bd0e13-5cb5-4ca4-b0c2-981e1ed71258
-- title:
--   P2 M Ground Theory Heights  Heights Model finite integral Closure fraction Ring of char Zero ff051fc57786: P2 M Ground Theory Heights  Heights Model finite integral Closure fraction Ring of char Zero
-- statement:
--   The P2 M Ground Theory Heights  Heights Model finite integral Closure fraction Ring of char Zero ff051fc57786 construction uses the P2 M Ground Theory Heights  Heights Model finite integral Closure fraction Ring of char Zero ff051fc57786 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteIntegralClosureCharZero.lean#L160-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteIntegralClosureCharZero.lean#L160-L164

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

theorem P2M_GroundTheory_Heights__Heights_Model_finite_integralClosure_fractionRing_of_charZero_ff051fc57786
    (A : Type*) [CommRing A] [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] :
    Module.Finite A (integralClosure A K) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«finite_integralClosure_fractionRing_of_charZero» := P2M_GroundTheory_Heights__Heights_Model_finite_integralClosure_fractionRing_of_charZero_ff051fc57786
