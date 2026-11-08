-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_sum_lpsPrefixTerm_filter_backtracking_add_two
-- name    : QEC.Coding.TannerLiftedProduct.sum_lpsPrefixTerm_filter_backtracking_add_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:25:45.586422+00:00
-- url     : https://prove2.me/theorems/50eaf98d-9786-4dc4-b611-6ee5a72a242d
-- title:
--   Tanner Lifted Product: sum lps Prefix Term filter backtracking add two
-- statement:
--   The backtracking part of a prefixed sphere is `p` copies of the sphere
--   two radii below.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L554-L591
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L554-L591

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.sum_lpsPrefixTerm_filter_backtracking_add_two
    (a : LPSResiduePrime p) (n : ℕ) :
    (∑ pair ∈ Finset.univ with ¬LPSPrefixIsReduced a (n + 1) pair,
      lpsPrefixTerm a pair) =
      p • lpsReducedWordElement a (n + 1) := by sorry
