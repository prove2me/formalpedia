-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseRationalInfinityTransport_rationalDifferentialInvolution_differential
-- name    : QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport.rationalDifferentialInvolution_differential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:37:32.355748+00:00
-- url     : https://prove2.me/theorems/6c7e3257-8bfa-46d1-b4ce-639055ee36f8
-- title:
--   Inverse Rational Infinity Transport: rational Differential Involution differential
-- statement:
--   Coordinate inversion sends an exact differential to the differential of
--   the inverted rational function.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/InvolutionResidueTransport.lean#L98-L120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/InvolutionResidueTransport.lean#L98-L120

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

theorem QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport.rationalDifferentialInvolution_differential (f : RatFunc k) :
    rationalDifferentialInvolution (k := k) (differential k (RatFunc k) f) =
      differential k (RatFunc k) (InverseAffinePlace.rationalInvolution k f) := by sorry
