-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_localDerivativeLattice_eq_span_uniformizerDerivative
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.localDerivativeLattice_eq_span_uniformizerDerivative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:23:40.736509+00:00
-- url     : https://prove2.me/theorems/c3858244-71bc-4756-b3f8-782ed89c5afe
-- title:
--   Function Field Differential: local Derivative Lattice eq span uniformizer Derivative
-- statement:
--   The derivative of the normalized valuation uniformizer generates the
--   actual local derivative lattice.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/LocalUniformizerDerivative.lean#L192-L210
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/LocalUniformizerDerivative.lean#L192-L210

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_CanonicalDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalLogarithmicDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalUniformizerDerivative
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.localDerivativeLattice_eq_span_uniformizerDerivative
    (P : GlobalPlace k F) :
    localDerivativeLattice (k := k) (F := F) P =
      Submodule.span P.valuationRing
        ({functionFieldDerivation (k := k) (F := F)
          (P.uniformizerInValuationRing : F)} : Set F) := by sorry
