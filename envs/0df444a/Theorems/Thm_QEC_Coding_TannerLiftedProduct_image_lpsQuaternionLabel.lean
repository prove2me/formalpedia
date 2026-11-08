-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_image_lpsQuaternionLabel
-- name    : QEC.Coding.TannerLiftedProduct.image_lpsQuaternionLabel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:58:29.511199+00:00
-- url     : https://prove2.me/theorems/769814e5-f70b-40a2-bc06-79e4d1678640
-- title:
--   Tanner Lifted Product: image lps Quaternion Label
-- statement:
--   The image of the fixed direction type is exactly the previously defined
--   finite generator set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L80-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L80-L84

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.image_lpsQuaternionLabel (a : LPSResiduePrime p) :
    Finset.univ.image (lpsQuaternionLabel a) =
      lpsQuaternionGeneratorsPSL a := by sorry
