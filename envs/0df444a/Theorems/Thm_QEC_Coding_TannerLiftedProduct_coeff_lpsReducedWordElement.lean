-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsReducedWordElement
-- name    : QEC.Coding.TannerLiftedProduct.coeff_lpsReducedWordElement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:26:23.661819+00:00
-- url     : https://prove2.me/theorems/7d4e4738-fdef-4ef6-be53-8a5c6636714d
-- title:
--   Tanner Lifted Product: coeff lps Reduced Word Element
-- statement:
--   A coefficient of the reduced-word element counts reduced words with the
--   chosen finite group product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L620-L630
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L620-L630

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.coeff_lpsReducedWordElement
    (a : LPSResiduePrime p) (n : ℕ)
    (g : PSL(2, ZMod a.q)) :
    (lpsReducedWordElement a n).coeff g =
      (((lpsReducedWords a.degreePrime.pos n).filter fun word =>
        cayleyVectorWordProduct (lpsQuaternionLabel a) word = g).card : ℂ) := by sorry
