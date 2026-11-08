-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_fintype_card_lpsClosedAlternatingReducedWord
-- name    : QEC.Coding.TannerLiftedProduct.fintype_card_lpsClosedAlternatingReducedWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:35:49.437578+00:00
-- url     : https://prove2.me/theorems/4061b315-fa78-476d-8f57-8a398b993075
-- title:
--   Tanner Lifted Product: fintype card lps Closed Alternating Reduced Word
-- statement:
--   The recursive closed normal-form subtype is counted by the existing
--   alternating closed reduced-word count `L_n(e,e)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceNormalForm.lean#L422-L461
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceNormalForm.lean#L422-L461

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeReducedWords
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceNormalForm
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.fintype_card_lpsClosedAlternatingReducedWord
    (a : LPSResiduePrime p) (n : ℕ) :
    Fintype.card (LPSClosedAlternatingReducedWord a n) =
      lpsAlternatingClosedReducedWordCount a n := by sorry
