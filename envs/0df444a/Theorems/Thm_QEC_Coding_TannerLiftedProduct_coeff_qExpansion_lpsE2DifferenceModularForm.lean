-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_qExpansion_lpsE2DifferenceModularForm
-- name    : QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsE2DifferenceModularForm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:14:53.591117+00:00
-- url     : https://prove2.me/theorems/509d4b07-e6e1-4619-b434-04a4c32605af
-- title:
--   Tanner Lifted Product: coeff q Expansion lps E2 Difference Modular Form
-- statement:
--   The genuine modular form retains the proved divisor-difference coefficients.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEisensteinDifference.lean#L281-L283
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEisensteinDifference.lean#L281-L283

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsE2DifferenceModularForm (m : ℕ) (hm : 0 < m) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsE2DifferenceModularForm m hm))=
      lpsE2DifferenceCoefficient m n := by sorry
