-- Prove2me | Theorems.Thm_RGMISFast_eq_28
-- name    : RGMISFast.eq_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:28:51.585094+00:00
-- url     : https://prove2.me/theorems/aa3f5acd-3e17-41f0-ae76-55c1de60d7ab
-- title:
--   Eq. (28): $2e\gamma(a)/a\le e^{-1}+2e^{-3}<1/2$ for $0<a\le a_0$
-- statement:
--   For $0<a\le a_0=e^2$ let $\gamma(a)=\mathbb E[\exp(-2\min\{a+X,a_0\}/a)]$ with $X\sim\mathrm{Exp}(1)$. Then
--   $$
--   \gamma(a)\le e^{-2}\,\mathbb E[e^{-2X/a}]+e^{-2a_0/a}=\frac{ae^{-2}}{a+2}+e^{-2a_0/a}\le ae^{-2}\Big(\frac12+\frac1{a_0}\Big),
--   $$
--   where $e^{-2/x}\le xe^{-2}$ for $0<x\le1$, and consequently
--   $$
--   \frac{2e\gamma(a)}{a}\le e^{-1}+2e^{-3}<\frac12. \tag{28}
--   $$
--
--   The bound makes the geometric series of (30) converge.
--
--   **Formalization Note** Every link of the chain is a separate clause; the expectations are integrals against Mathlib's Exp(1) law, of functions bounded by $1$ on its support.
--
--   Differences from the source: none.
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, STOC 2027 submission (manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664), §6.2, eq. (28), p.24 (PDF p.26)

import Mathlib
import Definitions.Def_RGMISFast_gammaA

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RGMISFast

/-- Eq. (28) with the bound on `γ` (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at Every Node*,
STOC 2027 submission (manuscript sha256 e93cdfec…), §6.2, p.24): for `0 < a ≤ a₀`, splitting according to
whether `a + X ≤ a₀` gives `γ(a) ≤ e^{−2}E[e^{−2X/a}] + e^{−2a₀/a} = ae^{−2}/(a + 2) + e^{−2a₀/a}
≤ ae^{−2}(1/2 + 1/a₀)`, using `e^{−2/x} ≤ xe^{−2}` for `0 < x ≤ 1`; since `a₀ = e²`,
`2eγ(a)/a ≤ e^{−1} + 2e^{−3} < 1/2`.

**Formalization Note** Every link of the chain is a separate clause. `E[e^{−2X/a}]` is the Bochner
integral against `expMeasure 1`; the integrand is bounded by `1` on `[0, ∞)`, which carries the
whole Exp(1) law, so the integral is a true expectation. -/
theorem eq_28 (a : ℝ) (ha : 0 < a) (ha0 : a ≤ a0) :
    gammaA a ≤ Real.exp (-2) * (∫ x, Real.exp (-2 * x / a) ∂(expMeasure 1)) +
        Real.exp (-2 * a0 / a) ∧
    Real.exp (-2) * (∫ x, Real.exp (-2 * x / a) ∂(expMeasure 1)) + Real.exp (-2 * a0 / a) =
        a * Real.exp (-2) / (a + 2) + Real.exp (-2 * a0 / a) ∧
    a * Real.exp (-2) / (a + 2) + Real.exp (-2 * a0 / a) ≤ a * Real.exp (-2) * (1 / 2 + 1 / a0) ∧
    (∀ x : ℝ, 0 < x → x ≤ 1 → Real.exp (-2 / x) ≤ x * Real.exp (-2)) ∧
    2 * Real.exp 1 * gammaA a / a ≤ Real.exp (-1) + 2 * Real.exp (-3) ∧
    Real.exp (-1) + 2 * Real.exp (-3) < 1 / 2 := by sorry

end RGMISFast
