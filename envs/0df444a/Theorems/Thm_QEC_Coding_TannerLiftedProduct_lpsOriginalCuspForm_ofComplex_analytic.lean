-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspForm_ofComplex_analytic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspForm_ofComplex_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:46:42.170483+00:00
-- url     : https://prove2.me/theorems/c233fb2f-36a0-496a-9f9b-b69cec6dacc1
-- title:
--   Tanner Lifted Product: lps Original Cusp Form of Complex analytic
-- statement:
--   The original cusp form is complex analytic in each upper-half-plane coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialCoefficients.lean#L182-L190
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialCoefficients.lean#L182-L190

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspQDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspForm_ofComplex_analytic (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (τ : ℍ) :
    AnalyticAt ℂ ((f : ℍ→ℂ)∘UpperHalfPlane.ofComplex) (τ:ℂ) := by sorry
