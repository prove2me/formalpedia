-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_integralClosure_mvPolynomial_of_isSeparable_f40b322046a9
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_integralClosure_mvPolynomial_of_isSeparable_f40b322046a9
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:20.633073+00:00
-- url     : https://prove2.me/theorems/66a812be-d466-466e-a6c5-51cf0576ee98
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers finite integral Closure mv Polynomial of is Separable f40b322046a9: P2 M Ground Theory Heights  Heights Field Numbers finite integral Closure mv Polyn
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers finite integral Closure mv Polynomial of is Separable f40b322046a9 construction uses the P2 M Ground Theory Heights  Heights Field Numbers finite integral Closure mv Polynomial of is Separable f40b322046a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/NoetherReduction.lean#L84-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/NoetherReduction.lean#L84-L92

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_integralClosure_mvPolynomial_of_isSeparable_f40b322046a9 (k : Type u) [Field k] (s : ℕ)
    (L : Type u) [Field L] [Algebra (FractionRing (MvPolynomial (Fin s) k)) L]
    [FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) L]
    [Algebra.IsSeparable (FractionRing (MvPolynomial (Fin s) k)) L]
    [Algebra (MvPolynomial (Fin s) k) L]
    [IsScalarTower (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) L] :
    Module.Finite (MvPolynomial (Fin s) k) (integralClosure (MvPolynomial (Fin s) k) L) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«finite_integralClosure_mvPolynomial_of_isSeparable» := P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_integralClosure_mvPolynomial_of_isSeparable_f40b322046a9
