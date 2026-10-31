-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P12_finite_general_perfect
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P12.finite_general_perfect
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:44:59.117087+00:00
-- url     : https://prove2.me/theorems/f4df923c-2d54-4666-8a1a-5167e15d1016
-- title:
--   §II (12)–(17): general finite shift-resistant code
-- statement:
--   Let $r_1,r_2,n$ be positive integers and $d=r_1r_2n$ with $n<d$. Define
--
--   $$J|j\rangle=\frac1{\sqrt{r_2}}\sum_{k=0}^{r_2-1}|r_1(j+nk)\rangle,\qquad0\le j<n.$$
--
--   Then $J$ is an isometry onto the common $+1$ eigenspace of $X^{r_1n},Z^{r_2n}$. The operators $X^{r_1},Z^{r_2}$ implement the logical cyclic shift and clock. The $r_1r_2$ half-open syndrome sectors are orthonormal copies of the logical space and exhaust the ambient space. One CPTP recovery corrects every operator in the span of $X^aZ^b$ with $|a|<r_1/2$, $|b|<r_2/2$, with the exact KL inner products stated explicitly.
--
--   This separates perfection of the full syndrome partition from the potentially smaller strict central correction window.
-- source:
--   Encoding a qubit in an oscillator, arXiv:quant-ph/0008040v3, PDF p. 3, §II (12)–(17): general finite shift-resistant code

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P12

noncomputable section

open scoped BigOperators

open MeasureTheory Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

namespace QAlgorithms.Papers.Independent.Intakenext100.P12

/-- Section II (12)–(17), PDF pp.3–4: the general finite shift-resistant code.
All syndrome sectors partition the space; the strict central window need not be complete.
The source explicitly considers a proper encoding n<d (PDF p.3). -/
theorem finite_general_perfect (d r1 r2 n : ℕ) [NeZero d]
    (hr1 : 0 < r1) (hr2 : 0 < r2) (hn : 0 < n) (hd : d = r1 * r2 * n)
    (hproper : n < d) :
    FiniteCodeConclusion d r1 r2 n := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P12

end
