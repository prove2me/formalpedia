-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lt_lpsResiduePrimeSequence_q
-- name    : QEC.Coding.TannerLiftedProduct.lt_lpsResiduePrimeSequence_q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:41:09.331221+00:00
-- url     : https://prove2.me/theorems/419af6cd-0a31-4494-b8df-563318944d7a
-- title:
--   Tanner Lifted Product: lt lps Residue Prime Sequence q
-- statement:
--   The Tanner Lifted Product construction uses the lt lps Residue Prime Sequence q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L36-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L36-L39

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lt_lpsResiduePrimeSequence_q
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    n < (lpsResiduePrimeSequence hp hp4 n).q := by sorry
