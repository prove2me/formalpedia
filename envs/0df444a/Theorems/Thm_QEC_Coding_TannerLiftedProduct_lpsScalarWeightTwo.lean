-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsScalarWeightTwo
-- name    : QEC.Coding.TannerLiftedProduct.lpsScalarWeightTwo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:03:50.278352+00:00
-- url     : https://prove2.me/theorems/6b59c64c-3f51-4b43-8501-7f6005bff6ec
-- title:
--   Tanner Lifted Product: lps Scalar Weight Two
-- statement:
--   Every nonzero real scalar matrix acts trivially on arbitrary weight-two slash functions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeAdjointDensities.lean#L16-L21
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeAdjointDensities.lean#L16-L21

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeAdjointDensities
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsScalarWeightTwo (f : ℍ → ℂ) (u : ℝˣ) :
    (f ∣[(2 : ℤ)] Matrix.GeneralLinearGroup.scalar (Fin 2) u) = f := by sorry
