-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeUpperGL_finite_action
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeUpperGL_finite_action
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:17:52.9102+00:00
-- url     : https://prove2.me/theorems/a55c3c21-15b1-4a79-9c3f-7b2b3ed55123
-- title:
--   Tanner Lifted Product: lps Hecke Upper GL finite action
-- statement:
--   The finite representative acts by the actual map z to (z+j)/p.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCoefficients.lean#L28-L33
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCoefficients.lean#L28-L33

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeUpperGL_finite_action (p : ℕ) [Fact p.Prime] (j : Fin p) (z : ℍ) :
    ((lpsHeckeUpperGL ℝ p (some j) • z:ℍ):ℂ)=((z:ℂ)+(j.val:ℂ))/(p:ℂ) := by sorry
