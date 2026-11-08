-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsRightCayleyGraph_isRegular
-- name    : QEC.Coding.TannerLiftedProduct.lpsRightCayleyGraph_isRegular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:59:37.572432+00:00
-- url     : https://prove2.me/theorems/f3d223ca-3902-4133-96a5-0e092738e6c2
-- title:
--   Tanner Lifted Product: lps Right Cayley Graph is Regular
-- statement:
--   The labelled Cayley multigraph is regular of degree equal to the shell
--   cardinality; Jacobi's theorem will identify this number with `p+1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L190-L196
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L190-L196

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsRightCayleyGraph_isRegular
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    SmallSetExpansion.IsRegular
      (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n))
      (lpsQuaternionShell p).card := by sorry
