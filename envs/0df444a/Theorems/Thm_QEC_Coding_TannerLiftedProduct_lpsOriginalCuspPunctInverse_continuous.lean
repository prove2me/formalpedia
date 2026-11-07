-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspPunctInverse_continuous
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspPunctInverse_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:42:12.133911+00:00
-- url     : https://prove2.me/theorems/60ec7c07-d792-4e96-8fc4-6661cb716864
-- title:
--   Tanner Lifted Product: lps Original Cusp Punct Inverse continuous
-- statement:
--   The true inverse punctured coordinate is continuous in the ORIGINAL quotient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L284-L286
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L284-L286

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspPunctInverse_continuous (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    Continuous (lpsOriginalCuspPunctInverse N ρ) := by sorry
