-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticEisensteinCusp_delta
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticEisensteinCusp_delta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:50:45.799429+00:00
-- url     : https://prove2.me/theorems/5cc28ffd-e870-4ec6-be87-1b9a45113081
-- title:
--   Tanner Lifted Product: lps Quadratic Eisenstein Cusp delta
-- statement:
--   The nontrivial character sum selects the unique root of the genuine finite-field linear expression.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L183-L207
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L183-L207

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticEisensteinCusp_delta (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (A D : ZMod q) (hD : D≠0) :
    (∑ r : ZMod q,lpsQuadraticE2Character q r*(if A+r*D=0 then (q:ℂ)^2 else 1))=
      ((q:ℂ)^2-1)*lpsQuadraticE2Character q (-A/D) := by sorry
