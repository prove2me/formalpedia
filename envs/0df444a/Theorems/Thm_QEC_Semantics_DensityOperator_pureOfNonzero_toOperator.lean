-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
-- name    : QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:00:39.684703+00:00
-- url     : https://prove2.me/theorems/66694f3e-4d05-4dc1-ad17-d87a07407835
-- title:
--   Density Operator: pure Of Nonzero to Operator
-- statement:
--   The Density Operator construction uses the pure Of Nonzero to Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L89-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L89-L94

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped ComplexOrder
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

theorem QEC.Semantics.DensityOperator.pureOfNonzero_toOperator (x : H) (hx : x ≠ 0) :
    (pureOfNonzero x hx).toOperator =
      (inner Complex x x)⁻¹ •
        (((InnerProductSpace.rankOne Complex x x : H →L[Complex] H) :
          H →ₗ[Complex] H)) := by sorry

attribute [defeq] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
