-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_finite_integralClosure_mvPolynomial_a1f9e8023895
-- name    : P2M_GroundTheory_Heights__Heights_Model_finite_integralClosure_mvPolynomial_a1f9e8023895
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:13.473063+00:00
-- url     : https://prove2.me/theorems/3d9e74dc-4c68-4808-992e-56c0a0f64a45
-- title:
--   P2 M Ground Theory Heights  Heights Model finite integral Closure mv Polynomial a1f9e8023895: P2 M Ground Theory Heights  Heights Model finite integral Closure mv Polynomial a1f9e8023895
-- statement:
--   The P2 M Ground Theory Heights  Heights Model finite integral Closure mv Polynomial a1f9e8023895 construction uses the P2 M Ground Theory Heights  Heights Model finite integral Closure mv Polynomial a1f9e8023895 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteIntegralClosureCharP.lean#L80-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteIntegralClosureCharP.lean#L80-L130

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

theorem P2M_GroundTheory_Heights__Heights_Model_finite_integralClosure_mvPolynomial_a1f9e8023895 (p : ℕ) [Fact p.Prime] (s : ℕ)
    (F : Type*) [Field F] [Algebra (MvPolynomial (Fin s) (ZMod p)) F]
    [IsFractionRing (MvPolynomial (Fin s) (ZMod p)) F]
    (L : Type*) [Field L] [Algebra F L] [FiniteDimensional F L]
    [Algebra (MvPolynomial (Fin s) (ZMod p)) L]
    [IsScalarTower (MvPolynomial (Fin s) (ZMod p)) F L] :
    Module.Finite (MvPolynomial (Fin s) (ZMod p))
      (integralClosure (MvPolynomial (Fin s) (ZMod p)) L) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«finite_integralClosure_mvPolynomial» := P2M_GroundTheory_Heights__Heights_Model_finite_integralClosure_mvPolynomial_a1f9e8023895
