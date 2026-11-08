-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsReducedWordElement_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsReducedWordElement_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:23:26.575926+00:00
-- url     : https://prove2.me/theorems/6b799fdc-96e1-42e8-a2a3-926ce8feb57a
-- title:
--   Tanner Lifted Product: lps Reduced Word Element zero
-- statement:
--   The Tanner Lifted Product construction uses the lps Reduced Word Element zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L698-L713
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L698-L713

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsReducedWordElement_zero
    (a : LPSResiduePrime p) :
    lpsReducedWordElement a 0 = 1 := by sorry
