-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegerCircleThinBox_no_three_distinct
-- name    : QEC.Coding.TannerLiftedProduct.lpsIntegerCircleThinBox_no_three_distinct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:49:38.045084+00:00
-- url     : https://prove2.me/theorems/7dacd7d9-89d0-4659-8f3d-1cfa64eef28b
-- title:
--   Tanner Lifted Product: lps Integer Circle Thin Box no three distinct
-- statement:
--   The Tanner Lifted Product construction uses the lps Integer Circle Thin Box no three distinct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L141-L154
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L141-L154

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsIntegerCircleThinBox_no_three_distinct
    (a b c : ℤ × ℤ) (n L : ℤ) (hn : 0 ≤ n) (hL : 0 ≤ L) (hsmall : 2*L^6<n)
    (ha : a.1^2+a.2^2=n) (hb : b.1^2+b.2^2=n) (hc : c.1^2+c.2^2=n)
    (habx : |b.1-a.1| ≤ L) (haby : |b.2-a.2| ≤ L)
    (hacx : |c.1-a.1| ≤ L) (hacy : |c.2-a.2| ≤ L)
    (hbcx : |c.1-b.1| ≤ L) (hbcy : |c.2-b.2| ≤ L) :
    a=b ∨ a=c ∨ b=c := by sorry
