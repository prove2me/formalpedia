-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseRationalInfinityTransport_rationalDifferentialInvolution_smul
-- name    : QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport.rationalDifferentialInvolution_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:37:32.901234+00:00
-- url     : https://prove2.me/theorems/a847c2ce-23a9-4b38-a39e-ed9cbae46e9c
-- title:
--   Inverse Rational Infinity Transport: rational Differential Involution smul
-- statement:
--   The differential involution is semilinear for the rational involution.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/InvolutionResidueTransport.lean#L124-L139
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/InvolutionResidueTransport.lean#L124-L139

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_RationalInfinityTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueCoordinate
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InvolutionResidueTransport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport
open scoped Polynomial RatFunc WithZero
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
omit [Finite k]

theorem QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport.rationalDifferentialInvolution_smul (f : RatFunc k)
    (omega : Differential k (RatFunc k)) :
    rationalDifferentialInvolution (k := k) (f • omega) =
      InverseAffinePlace.rationalInvolution k f •
        rationalDifferentialInvolution (k := k) omega := by sorry
