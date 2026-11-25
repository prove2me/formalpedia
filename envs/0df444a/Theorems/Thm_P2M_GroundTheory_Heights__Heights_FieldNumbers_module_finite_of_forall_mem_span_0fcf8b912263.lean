-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_module_finite_of_forall_mem_span_0fcf8b912263
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_module_finite_of_forall_mem_span_0fcf8b912263
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:56:04.674971+00:00
-- url     : https://prove2.me/theorems/c07c0991-9ed3-4cea-8a42-47156079dfbc
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers module finite of forall mem span 0fcf8b912263: P2 M Ground Theory Heights  Heights Field Numbers module finite of forall mem span 0fcf8b912263
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers module finite of forall mem span 0fcf8b912263 construction uses the P2 M Ground Theory Heights  Heights Field Numbers module finite of forall mem span 0fcf8b912263 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSemilocalFinite.lean#L17-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSemilocalFinite.lean#L17-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsLocalIntegralClosureFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSemilocalFiniteRank
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSemilocalFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_module_finite_of_forall_mem_span_0fcf8b912263 {A A' B L : Type*} [CommRing A] [IsNoetherianRing A]
    [CommRing A'] [CommRing B] [Algebra A B] [CommRing L] [Algebra A' L] (φ : A →+* A')
    (hφ : Function.Surjective φ) (ψ : B →+* L) (hψ : Function.Injective ψ)
    (hcomm : ∀ a b, ψ (algebraMap A B a * b) = algebraMap A' L (φ a) * ψ b) (s : Finset L)
    (h : ∀ b, ψ b ∈ Submodule.span A' (s : Set L)) : Module.Finite A B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«module_finite_of_forall_mem_span» := P2M_GroundTheory_Heights__Heights_FieldNumbers_module_finite_of_forall_mem_span_0fcf8b912263
