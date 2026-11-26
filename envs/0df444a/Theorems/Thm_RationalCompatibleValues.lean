-- Prove2me | Theorems.Thm_RationalCompatibleValues
-- name    : RationalCompatibleValues
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:52:26.561022+00:00
-- url     : https://prove2.me/theorems/89e185c4-0d44-5a70-aed1-a66cc1587eca
-- title:
--   Rational Compatible Values: Rational Compatible Values
-- statement:
--   Paper Lemma A.1, the rational-rounding step (paper.tex 1646--1681). Given a `K`-Lipschitz
--   `π : E → ℝ` with `K > 0`, finitely many points `e j` that are `r`-separated whenever distinct, and
--   a rounding tolerance `δ ≤ ε r K / 4`, one can choose a rational Lipschitz constant `C` with
--   `(1 - ε/2) K ≤ C ≤ K` and rational values `c j` within `δ` of the damped values `(1 - ε) π (e j)`,
--   such that the `c j` are *compatible* with `C`: `|c j - c j'| ≤ C d(e j, e j')` for all `j, j'`.
--   This is the hypothesis consumed by `ConeInterpolation`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/RationalCompatibleValues.lean#L12-L81
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/RationalCompatibleValues.lean#L12-L81

import Definitions.Def_Tablet_Preamble
import Definitions.Def_Tablet_RationalCompatibleValues
set_option autoImplicit false
open scoped NNReal

theorem RationalCompatibleValues {E : Type*} [MetricSpace E] {k : ℕ}
    (pi : E → ℝ) (K : ℝ≥0) (hpi : LipschitzWith K pi) (hK : 0 < (K : ℝ))
    (e : Fin (k + 1) → E) (eps r delta : ℝ)
    (heps : 0 < eps) (heps1 : eps < 1) (hr : 0 < r)
    (hsep : ∀ j j', e j ≠ e j' → r ≤ dist (e j) (e j'))
    (hdelta : 0 < delta) (hdle : delta ≤ eps * r * (K : ℝ) / 4) :
    ∃ (c : Fin (k + 1) → ℚ) (C : ℚ),
      (1 - eps / 2) * (K : ℝ) ≤ (C : ℝ) ∧ (C : ℝ) ≤ (K : ℝ) ∧
      (∀ j, |(c j : ℝ) - (1 - eps) * pi (e j)| ≤ delta) ∧
      (∀ j j', |(c j : ℝ) - (c j' : ℝ)| ≤ (C : ℝ) * dist (e j) (e j')) := by sorry
