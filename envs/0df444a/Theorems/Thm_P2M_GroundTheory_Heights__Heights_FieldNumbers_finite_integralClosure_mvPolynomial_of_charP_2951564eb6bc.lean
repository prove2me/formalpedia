-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_integralClosure_mvPolynomial_of_charP_2951564eb6bc
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_integralClosure_mvPolynomial_of_charP_2951564eb6bc
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:14.778604+00:00
-- url     : https://prove2.me/theorems/fce17707-bed8-4048-89dc-fe11a5b818f9
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers finite integral Closure mv Polynomial of char P 2951564eb6bc: P2 M Ground Theory Heights  Heights Field Numbers finite integral Closure mv Polynomial
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers finite integral Closure mv Polynomial of char P 2951564eb6bc construction uses the P2 M Ground Theory Heights  Heights Field Numbers finite integral Closure mv Polynomial of char P 2951564eb6bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/NoetherCharP.lean#L15-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/NoetherCharP.lean#L15-L182

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_NoetherReduction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_NoetherCharPLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_NoetherCharP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Polynomial
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
universe u
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_integralClosure_mvPolynomial_of_charP_2951564eb6bc (k : Type u) [Field k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (s : ℕ) (L : Type u) [Field L] [Algebra (FractionRing (MvPolynomial (Fin s) k)) L]
    [FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) L]
    [Algebra (MvPolynomial (Fin s) k) L]
    [IsScalarTower (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) L] :
    Module.Finite (MvPolynomial (Fin s) k) (integralClosure (MvPolynomial (Fin s) k) L) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«finite_integralClosure_mvPolynomial_of_charP» := P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_integralClosure_mvPolynomial_of_charP_2951564eb6bc
