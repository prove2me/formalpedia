-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsClosedWords_eq_sum_closedWordFiber
-- name    : QEC.Coding.TannerLiftedProduct.card_lpsClosedWords_eq_sum_closedWordFiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:22:08.203732+00:00
-- url     : https://prove2.me/theorems/9f75d4f5-5861-4412-9f56-764c9c0a3113
-- title:
--   Tanner Lifted Product: card lps Closed Words eq sum closed Word Fiber
-- statement:
--   Closed words decompose exactly into the fibres of their quaternion
--   congruence-shell image, including shell points with empty fibre.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleyWordTrace.lean#L188-L202
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleyWordTrace.lean#L188-L202

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord
import Mathlib.Data.Fintype.Vector
import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v} [Group G] [Fintype W]
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.card_lpsClosedWords_eq_sum_closedWordFiber
    (a : LPSResiduePrime p) (n : ℕ) :
    (lpsClosedWords a n).card =
      ∑ t : {t // t ∈ lpsTraceCongruenceShell a.q (p ^ n)},
        (lpsClosedWordFiber a n t).card := by sorry
