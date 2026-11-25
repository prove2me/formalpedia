-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_finite_integralClosure_of_charP_65f7d60edb2f
-- name    : P2M_GroundTheory_Heights__Heights_Model_finite_integralClosure_of_charP_65f7d60edb2f
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:15.854801+00:00
-- url     : https://prove2.me/theorems/31a09192-f126-4339-8fcb-cf36768afa37
-- title:
--   P2 M Ground Theory Heights  Heights Model finite integral Closure of char P 65f7d60edb2f: P2 M Ground Theory Heights  Heights Model finite integral Closure of char P 65f7d60edb2f
-- statement:
--   The P2 M Ground Theory Heights  Heights Model finite integral Closure of char P 65f7d60edb2f construction uses the P2 M Ground Theory Heights  Heights Model finite integral Closure of char P 65f7d60edb2f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteIntegralClosureCharP.lean#L132-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteIntegralClosureCharP.lean#L132-L202

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureCharP
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

theorem P2M_GroundTheory_Heights__Heights_Model_finite_integralClosure_of_charP_65f7d60edb2f (p : ℕ) [Fact p.Prime]
    (A : Type*) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A] [CharP A p]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A K L] :
    Module.Finite A (integralClosure A L) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«finite_integralClosure_of_charP» := P2M_GroundTheory_Heights__Heights_Model_finite_integralClosure_of_charP_65f7d60edb2f
