-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseDifferentialTraceTransport_transported_fieldTrace_eq_rationalInvolution
-- name    : QEC.Coding.AlgebraicGeometry.InverseDifferentialTraceTransport.transported_fieldTrace_eq_rationalInvolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:38:33.075577+00:00
-- url     : https://prove2.me/theorems/3c072b01-3738-4d46-a144-60c33a8bdaeb
-- title:
--   Inverse Differential Trace Transport: transported field Trace eq rational Involution
-- statement:
--   Field trace for the transported inverse-coordinate algebra is the
--   rational involution of the original field trace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Inverse/DifferentialTraceTransport.lean#L126-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Inverse/DifferentialTraceTransport.lean#L126-L161

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
omit [Finite k]

theorem QEC.Coding.AlgebraicGeometry.InverseDifferentialTraceTransport.transported_fieldTrace_eq_rationalInvolution (x : F) :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : IsScalarTower k k⟮X⟯ F := inverseConstantScalarTower
      (oldPolynomialAlgebra := oldPolynomialAlgebra)
      (oldRationalAlgebra := oldRationalAlgebra)
      (oldScalarTower := oldScalarTower) k F
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    Algebra.trace k⟮X⟯ F x =
      InverseAffinePlace.rationalInvolution k
        (@Algebra.trace k⟮X⟯ F _ _ oldRationalAlgebra x) := by sorry
