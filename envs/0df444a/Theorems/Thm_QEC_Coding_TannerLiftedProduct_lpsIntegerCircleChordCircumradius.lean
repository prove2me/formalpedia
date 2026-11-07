-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegerCircleChordCircumradius
-- name    : QEC.Coding.TannerLiftedProduct.lpsIntegerCircleChordCircumradius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:47:56.911242+00:00
-- url     : https://prove2.me/theorems/cc42b9e0-ca51-4d9a-8882-bab6ed982659
-- title:
--   Tanner Lifted Product: lps Integer Circle Chord Circumradius
-- statement:
--   The Tanner Lifted Product construction uses the lps Integer Circle Chord Circumradius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L73-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L73-L97

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsIntegerCircleChordCircumradius
    (a b c : ℤ × ℤ) (n : ℤ)
    (ha : a.1^2+a.2^2=n) (hb : b.1^2+b.2^2=n) (hc : c.1^2+c.2^2=n) :
    4*n*(lpsIntegerCircleChordDet a b c)^2 =
      lpsIntegerCircleSquaredDistance a b * lpsIntegerCircleSquaredDistance a c *
        lpsIntegerCircleSquaredDistance b c := by sorry
