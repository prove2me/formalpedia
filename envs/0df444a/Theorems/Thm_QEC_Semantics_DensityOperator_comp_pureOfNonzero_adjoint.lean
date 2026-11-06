-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_comp_pureOfNonzero_adjoint
-- name    : QEC.Semantics.DensityOperator.comp_pureOfNonzero_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:02:33.158972+00:00
-- url     : https://prove2.me/theorems/7e101201-1af0-4a14-8d0f-b62916bbdfa4
-- title:
--   Density Operator: comp pure Of Nonzero adjoint
-- statement:
--   The Density Operator construction uses the comp pure Of Nonzero adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L108-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L108-L114

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

theorem QEC.Semantics.DensityOperator.comp_pureOfNonzero_adjoint (A : Operator H) (x : H) (hx : x ≠ 0) :
    A.comp ((pureOfNonzero x hx).toOperator.comp (LinearMap.adjoint A)) =
      (inner Complex x x)⁻¹ •
        (((InnerProductSpace.rankOne Complex (A x) (A x) : H →L[Complex] H) :
          H →ₗ[Complex] H)) := by sorry
