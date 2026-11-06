-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseDifferentialTraceTransport_transported_functionFieldDifferentialTrace_eq_rationalDifferentialInvolution
-- name    : QEC.Coding.AlgebraicGeometry.InverseDifferentialTraceTransport.transported_functionFieldDifferentialTrace_eq_rationalDifferentialInvolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:38:37.264209+00:00
-- url     : https://prove2.me/theorems/d1887b48-ec8d-4ef8-bb22-9d5905f5f6e7
-- title:
--   Inverse Differential Trace Transport: transported function Field Differential Trace eq rational Differential Involution
-- statement:
--   The differential trace for the inverse-coordinate presentation is the
--   actual rational differential involution of the original trace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Inverse/DifferentialTraceTransport.lean#L165-L286
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Inverse/DifferentialTraceTransport.lean#L165-L286

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InvolutionResidueTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_DifferentialTraceTransport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.InverseDifferentialTraceTransport
open scoped Polynomial RatFunc
open FunctionFieldDifferential
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
variable [oldScalarTower : IsScalarTower k[X] k⟮X⟯ F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.InverseDifferentialTraceTransport.directConstantAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.InverseDifferentialTraceTransport.directConstantScalarTower
local notation3 "inverseRationalAlgebra" =>
  InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
local notation3 "inverseFunctionField" =>
  InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldFunctionField := oldFunctionField) k F
local notation3 "inverseIsSeparable" =>
  InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldSeparable := oldSeparable) k F

theorem QEC.Coding.AlgebraicGeometry.InverseDifferentialTraceTransport.transported_functionFieldDifferentialTrace_eq_rationalDifferentialInvolution
    (omega : Differential k F) :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : IsScalarTower k k⟮X⟯ F := inverseConstantScalarTower
      (oldPolynomialAlgebra := oldPolynomialAlgebra)
      (oldRationalAlgebra := oldRationalAlgebra)
      (oldScalarTower := oldScalarTower) k F
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    functionFieldDifferentialTrace (k := k) (F := F) omega =
      InverseRationalInfinityTransport.rationalDifferentialInvolution (k := k)
        (letI : Algebra k⟮X⟯ F := oldRationalAlgebra
         letI : IsScalarTower k k⟮X⟯ F := directConstantScalarTower
           (oldPolynomialAlgebra := oldPolynomialAlgebra)
           (oldRationalAlgebra := oldRationalAlgebra)
           (oldScalarTower := oldScalarTower) k F
         letI : _root_.FunctionField k F := oldFunctionField
         letI : Algebra.IsSeparable k⟮X⟯ F := oldSeparable
         functionFieldDifferentialTrace (k := k) (F := F) omega) := by sorry
