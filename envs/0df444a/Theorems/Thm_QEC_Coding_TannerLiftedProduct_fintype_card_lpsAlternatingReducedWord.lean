-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_fintype_card_lpsAlternatingReducedWord
-- name    : QEC.Coding.TannerLiftedProduct.fintype_card_lpsAlternatingReducedWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:04:49.471234+00:00
-- url     : https://prove2.me/theorems/7b81526d-21aa-47d4-9c68-fffe57d24f55
-- title:
--   Tanner Lifted Product: fintype card lps Alternating Reduced Word
-- statement:
--   The recursive normal-form type has exactly the alternating reduced-word
--   count defined from finite word spheres.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionNormalForm.lean#L46-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionNormalForm.lean#L46-L65

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimePowerCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.fintype_card_lpsAlternatingReducedWord
    (hp : 0 < p) (n : ℕ) :
    Fintype.card (LPSAlternatingReducedWord hp n) =
      lpsAlternatingReducedWordCount hp n := by sorry
