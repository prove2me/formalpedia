-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2DifferenceCoefficient_of_not_dvd
-- name    : QEC.Coding.TannerLiftedProduct.lpsE2DifferenceCoefficient_of_not_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:27:23.562196+00:00
-- url     : https://prove2.me/theorems/7f77d5ca-1e5e-42ea-a5a9-111a9164705d
-- title:
--   Tanner Lifted Product: lps E2 Difference Coefficient of not dvd
-- statement:
--   At nonzero indices outside dilation multiples the actual coefficient is the raw E2 divisor sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEisensteinDifference.lean#L290-L292
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEisensteinDifference.lean#L290-L292

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsE2DifferenceCoefficient_of_not_dvd (m n : ℕ) (hn : n≠0) (hnd : ¬m∣n) :
    lpsE2DifferenceCoefficient m n= -24*(ArithmeticFunction.sigma 1 n:ℂ) := by sorry
