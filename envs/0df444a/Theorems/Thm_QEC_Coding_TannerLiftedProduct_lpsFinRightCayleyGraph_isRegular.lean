-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFinRightCayleyGraph_isRegular
-- name    : QEC.Coding.TannerLiftedProduct.lpsFinRightCayleyGraph_isRegular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:00:26.334907+00:00
-- url     : https://prove2.me/theorems/aae753ea-289a-48a6-bd2a-f6619aab39ba
-- title:
--   Tanner Lifted Product: lps Fin Right Cayley Graph is Regular
-- statement:
--   In `Fin (p + 1)` coordinates the concrete LPS Cayley multigraph is
--   exactly `(p + 1)`-regular.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L253-L260
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L253-L260

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsFinRightCayleyGraph_isRegular
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hCount : (lpsQuaternionShell p).card = p + 1) (n : ℕ) :
    SmallSetExpansion.IsRegular
      (rightCayleyGraph (lpsFinQuaternionFamilyLabel hp hp4 hCount n))
      (p + 1) := by sorry
