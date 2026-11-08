-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_sum_lpsPrefixTerm_filter_backtracking_zero
-- name    : QEC.Coding.TannerLiftedProduct.sum_lpsPrefixTerm_filter_backtracking_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:27:06.384803+00:00
-- url     : https://prove2.me/theorems/aa7b81e3-50b5-4911-825b-45aad89a2151
-- title:
--   Tanner Lifted Product: sum lps Prefix Term filter backtracking zero
-- statement:
--   At radius one, the backtracking fibre has `p+1` choices because there is
--   no preceding letter to exclude.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L737-L784
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L737-L784

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.sum_lpsPrefixTerm_filter_backtracking_zero
    (a : LPSResiduePrime p) :
    (∑ pair ∈ Finset.univ with ¬LPSPrefixIsReduced a 0 pair,
      lpsPrefixTerm a pair) =
      (p + 1) • lpsReducedWordElement a 0 := by sorry
