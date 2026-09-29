-- Prove2me | Theorems.Thm_Real_tendsto_pow_log_div_pow_atTop
-- name    : Real.tendsto_pow_log_div_pow_atTop
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:18:13.675565+00:00
-- url     : https://prove2.me/theorems/cc66646b-9fed-4ce7-a7dc-de7d7a009234
-- title:
--   Logarithmic powers lose to polynomial powers: $(\log x)^b/x^a \to 0$ as $x\to\infty$ for $a>0$
-- statement:
--   Let $a,b\in\mathbb{R}$ with $a>0$. Then
--
--   $$\lim_{x\to\infty} \frac{(\log x)^{b}}{x^{a}} \;=\; 0.$$
--
--   That is, any fixed real power of the logarithm is eventually dominated by any fixed positive power of $x$; the exponent $b$ may be arbitrary (positive, zero, or negative) while only $a>0$ is required.
--
--   This is the standard growth-scale comparison between logarithmic and polynomial growth, stated for real exponents. In the Prime Number Theorem development it is invoked repeatedly to absorb the polylogarithmic losses — factors like $(\log T)^{9}$ from the zero-free-region bounds on $\zeta'/\zeta$ — into power savings $X^{\sigma-1}$ coming from contour position, when the parameters $T$ and $\varepsilon$ are chosen as functions of $X$ to produce the final error term $O\bigl(x\exp(-c(\log x)^{1/10})\bigr)$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean#L9-L17

import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

open Filter Real

theorem Real.tendsto_pow_log_div_pow_atTop (a : ℝ) (b : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun x ↦ log x ^ b / x^a) Filter.atTop (nhds 0) := by sorry
