-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeUpperGL_finite_qParam
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeUpperGL_finite_qParam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:17:44.423935+00:00
-- url     : https://prove2.me/theorems/13d813db-fd0a-4d2b-b3cb-02bf6699413f
-- title:
--   Tanner Lifted Product: lps Hecke Upper GL finite q Param
-- statement:
--   The actual translated nome splits into its finite additive phase and p-width nome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCoefficients.lean#L47-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCoefficients.lean#L47-L57

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeUpperGL_finite_qParam (p : ℕ) [Fact p.Prime] (j : Fin p) (z : ℍ) :
    Function.Periodic.qParam 1 ((lpsHeckeUpperGL ℝ p (some j) • z:ℍ):ℂ)=
      ZMod.stdAddChar (j.val:ZMod p)*Function.Periodic.qParam (p:ℝ) (z:ℂ) := by sorry
