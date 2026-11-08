-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_sum_lpsPrefixTerm_filter_reduced
-- name    : QEC.Coding.TannerLiftedProduct.sum_lpsPrefixTerm_filter_reduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:25:14.26212+00:00
-- url     : https://prove2.me/theorems/dbc71874-36d3-4053-860b-26dd9826c39d
-- title:
--   Tanner Lifted Product: sum lps Prefix Term filter reduced
-- statement:
--   The non-backtracking part of a prefixed sphere is the next sphere.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L517-L550
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L517-L550

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.sum_lpsPrefixTerm_filter_reduced
    (a : LPSResiduePrime p) (n : ℕ) :
    (∑ pair ∈ Finset.univ with LPSPrefixIsReduced a n pair,
      lpsPrefixTerm a pair) =
      lpsReducedWordElement a (n + 2) := by sorry
