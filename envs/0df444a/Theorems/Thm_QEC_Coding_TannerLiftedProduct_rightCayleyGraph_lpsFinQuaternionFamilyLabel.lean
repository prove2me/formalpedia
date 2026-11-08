-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightCayleyGraph_lpsFinQuaternionFamilyLabel
-- name    : QEC.Coding.TannerLiftedProduct.rightCayleyGraph_lpsFinQuaternionFamilyLabel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:41:36.502715+00:00
-- url     : https://prove2.me/theorems/1574ab25-ab13-4901-9f20-bb7b6becc086
-- title:
--   Tanner Lifted Product: right Cayley Graph lps Fin Quaternion Family Label
-- statement:
--   Direction reindexing leaves the concrete LPS Cayley multigraph exactly
--   unchanged.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L180-L186
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L180-L186

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.rightCayleyGraph_lpsFinQuaternionFamilyLabel
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hCount : (lpsQuaternionShell p).card = p + 1) (n : ℕ) :
    rightCayleyGraph (lpsFinQuaternionFamilyLabel hp hp4 hCount n) =
      rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n) := by sorry
