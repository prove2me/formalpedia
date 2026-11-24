-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_integralClosure_of_forall_mvPolynomial_4e8918a7d574
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_integralClosure_of_forall_mvPolynomial_4e8918a7d574
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:27.96981+00:00
-- url     : https://prove2.me/theorems/fcb65921-4736-4183-a1ab-e4186528a587
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers finite integral Closure of forall mv Polynomial 4e8918a7d574: P2 M Ground Theory Heights  Heights Field Numbers finite integral Closure of forall mv P
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers finite integral Closure of forall mv Polynomial 4e8918a7d574 construction uses the P2 M Ground Theory Heights  Heights Field Numbers finite integral Closure of forall mv Polynomial 4e8918a7d574 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/NoetherReduction.lean#L10-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/NoetherReduction.lean#L10-L82

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_integralClosure_of_forall_mvPolynomial_4e8918a7d574
    (k A : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A K L]
    (hpoly : ∀ (s : ℕ) (L' : Type u) [Field L'] [Algebra (FractionRing (MvPolynomial (Fin s) k)) L']
      [FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) L']
      [Algebra (MvPolynomial (Fin s) k) L']
      [IsScalarTower (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) L'],
      Module.Finite (MvPolynomial (Fin s) k) (integralClosure (MvPolynomial (Fin s) k) L')) :
    Module.Finite A (integralClosure A L) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«finite_integralClosure_of_forall_mvPolynomial» := P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_integralClosure_of_forall_mvPolynomial_4e8918a7d574
