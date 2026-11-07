-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_qExpansion_lpsQuadraticE2TwistModularForm
-- name    : QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsQuadraticE2TwistModularForm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:57:25.495711+00:00
-- url     : https://prove2.me/theorems/06fa849f-2a7b-4267-9601-c2d974259ca1
-- title:
--   Tanner Lifted Product: coeff q Expansion lps Quadratic E2 Twist Modular Form
-- statement:
--   The constructed modular form retains the actual character-weighted divisor coefficients.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinModularForm.lean#L340-L343
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinModularForm.lean#L340-L343

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsQuadraticE2TwistModularForm (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsQuadraticE2TwistModularForm q hq2)) =
      -24*(ArithmeticFunction.sigma 1 n:ℂ)*lpsQuadraticE2Character q (n:ZMod q) := by sorry
