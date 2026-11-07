-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2CuspFactor_matrix
-- name    : QEC.Coding.TannerLiftedProduct.lpsE2CuspFactor_matrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:00:20.987896+00:00
-- url     : https://prove2.me/theorems/f02b6b7e-cfbe-42aa-b221-b76f978ac9a1
-- title:
--   Tanner Lifted Product: lps E2 Cusp Factor matrix
-- statement:
--   Actual arithmetic column relations and determinant prove the real matrix factorization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCusps.lean#L133-L147
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCusps.lean#L133-L147

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsE2CuspFactor_matrix (g q r A B C D : ℝ) (hg : g≠0) (hq : q≠0)
    (ha : A*g=r+1) (hc : C*g=q) (hd : A*D-B*C=1) :
    !![r+1,r/q;q,1]=!![A,B;C,D]*!![g,D*r/q-B;0,g⁻¹] := by sorry
