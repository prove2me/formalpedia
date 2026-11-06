-- Prove2me | Theorems.Thm_QEC_Semantics_spectralSign_mul_of_isSymmetric
-- name    : QEC.Semantics.spectralSign_mul_of_isSymmetric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:25:38.963319+00:00
-- url     : https://prove2.me/theorems/95d0a73b-207b-419d-bbdc-be5f56d2a11d
-- title:
--   Semantics: spectral Sign mul of is Symmetric
-- statement:
--   The Semantics construction uses the spectral Sign mul of is Symmetric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L353-L369
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L353-L369

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]

theorem QEC.Semantics.spectralSign_mul_of_isSymmetric (A : Operator H) (hA : A.IsSymmetric) :
    spectralSign A * LinearMap.toContinuousLinearMap A =
      (LinearMap.toContinuousLinearMap A)⁺ +
        (LinearMap.toContinuousLinearMap A)⁻ := by sorry
