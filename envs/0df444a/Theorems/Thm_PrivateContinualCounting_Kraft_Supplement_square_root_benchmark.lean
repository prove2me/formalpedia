-- Prove2me | Theorems.Thm_PrivateContinualCounting_Kraft_Supplement_square_root_benchmark
-- name    : PrivateContinualCounting.Kraft.Supplement.square_root_benchmark
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:33:40.261377+00:00
-- url     : https://prove2.me/theorems/3eef55da-53f0-46b1-9826-e6e44a984ad9
-- title:
--   Lemma 2.4 — exact square-root benchmark constants
-- statement:
--   Let $c_j=4^{-j}\binom{2j}{j}$, $S(n)=\sum_{j<n}c_j^2$, and let $\gamma_E$ be Euler's constant. For every integer $n\ge1$,
--   $$1+\frac{\ln n+\gamma_E-1}{\pi}<S(n)\le1+\frac{\ln n+\gamma_E}{\pi}.$$
--   The strict lower inequality and both additive constants are retained. This fixes the square-root benchmark used to obtain the exact leading coefficient $1/\pi^2$ in Theorem 1.4.
--
--   Differences from the source: none.
-- source:
--   Kisung Park, STOC 2027 submission #86 (October 2026), p. 7, PDF p. 9, Lemma 2.4

import Definitions.Def_PrivateContinualCounting_Kraft_Supplement_Benchmarks

open MeasureTheory ProbabilityTheory Filter

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft.Supplement

/-- Lemma 2.4, with the strict lower inequality and exact additive constants. -/
theorem square_root_benchmark (n : ℕ) (hn : 1 ≤ n) :
    1 + (Real.log (n:ℝ) + Real.eulerMascheroniConstant - 1) / Real.pi < squareEnergy n ∧
    squareEnergy n ≤ 1 + (Real.log (n:ℝ) + Real.eulerMascheroniConstant) / Real.pi := by sorry

end PrivateContinualCounting.Kraft.Supplement
