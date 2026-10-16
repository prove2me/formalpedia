-- Prove2me | Theorems.Thm_SubsetShrink_BIC_tail_to_expectation
-- name    : SubsetShrink.BIC.tail_to_expectation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:27:22.335522+00:00
-- url     : https://prove2.me/theorems/d356ad5d-f00e-4814-bd83-0fe28f575197
-- title:
--   Proof of Corollary 3 (B.5), p. 42 — from W ≤ κ log(1/δ0) w.p. 1 − δ0/2 to E W ≤ κ/2
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $W:\Omega\to\mathbb R$ a random variable and $\kappa>0$. Suppose that for every $\delta_0\in(0,1)$,
--   $$P\big(W\le\kappa\log(1/\delta_0)\big)\ge1-\delta_0/2 .$$
--   Then $2P(W>w)\le e^{-w/\kappa}$ for every $w\ge0$, and
--   $$\mathbb E\,W^+=\mathbb E\max(W,0)\le\int_0^\infty P(W>w)\,dw\le\tfrac12\int_0^\infty e^{-w/\kappa}\,dw=\frac{\kappa}{2}.$$
--
--   The proof of Theorem 5 applies this with $\kappa$ a universal multiple of $\sigma^2$ and $W$ the excess of $\|f^*-X\hat\beta\|^2$ over $C$ times the oracle term, turning the high-probability bounds (56) and (58) into the expectation bounds of Theorem 5.
--
--   **Formalization Note** The page writes $\mathbb EW$ but bounds it through $P(W>w)$ for $w\ge0$ only, which is a bound on $\mathbb E W^+$; the statement's lower Lebesgue integral of $\max(W,0)$ (`∫⁻ ofReal W`) is exactly $\mathbb E W^+$, and it bounds $\mathbb EW$ whenever the latter is defined. In the paper $\kappa=c_0\sigma^2$.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 42, proof of Corollary 3 (B.5), displays 2P(W > w) ≤ e^{−w/[c0σ²]} and EW ≤ … ≤ c0σ²/2; invoked in B.13, p. 50

import Mathlib
import Definitions.Def_SubsetShrink_BIC_Model

namespace SubsetShrink.BIC

open MeasureTheory ProbabilityTheory

/-- Proof of Corollary 3 (B.5), p. 42: if `W ≤ κ log(1/δ0)` with probability at least `1 − δ0/2`
for every `δ0 ∈ (0, 1)`, then `2 P(W > w) ≤ e^{−w/κ}` for every `w ≥ 0`, and
`E[W⁺] ≤ κ/2` (here `κ = c0 σ²`). -/
theorem tail_to_expectation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (W : Ω → ℝ) (hW : Measurable W) (κ : ℝ) (hκ : 0 < κ)
    (h : ∀ δ0 : ℝ, 0 < δ0 → δ0 < 1 →
      1 - δ0 / 2 ≤ (μ {ω | W ω ≤ κ * Real.log (1 / δ0)}).toReal) :
    (∀ w : ℝ, 0 ≤ w → 2 * (μ {ω | w < W ω}).toReal ≤ Real.exp (-w / κ)) ∧
    ∫⁻ ω, ENNReal.ofReal (W ω) ∂μ ≤ ENNReal.ofReal (κ / 2) := by sorry

end SubsetShrink.BIC
