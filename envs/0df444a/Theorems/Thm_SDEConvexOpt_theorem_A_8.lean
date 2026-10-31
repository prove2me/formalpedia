-- Prove2me | Theorems.Thm_SDEConvexOpt_theorem_A_8
-- name    : SDEConvexOpt.theorem_A_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:25:15.327432+00:00
-- url     : https://prove2.me/theorems/5c034870-814c-47c7-981c-20dfc8aa19f4
-- title:
--   Theorem A.8 — an $L^p$-bounded continuous martingale, $p>1$, converges a.s. to some $M_\infty\in L^p$
-- statement:
--   Let $(M_t)_{t\ge0}$ be a real continuous martingale with respect to a filtration $(\mathcal F_t)$ on $(\Omega,\mathcal F,\mathbb P)$ such that
--   $$
--   \sup_{t\ge0}\mathbb E\big(|M_t|^p\big)<\infty\quad\text{for some } p>1 .
--   $$
--   Then there is a random variable $M_\infty$ with $\mathbb E(|M_\infty|^p)<\infty$ and $\lim_{t\to\infty}M_t=M_\infty$ almost surely.
--
--   In the proof of Theorem 3.1(iii) it makes the stochastic integral $\int_0^t\langle\sigma^\top(s,X(s))\nabla f(X(s)),dW(s)\rangle$ converge.
--
--   Differences from the source:
--   - encoding: "continuous" martingale; $\mathbb E|\cdot|^p$; random variable $M_\infty$ → a.s. continuous paths, Mathlib `Martingale`; lower Lebesgue integrals of $\|\cdot\|_e^p$ in `ℝ≥0∞`; a measurable $M_\infty:\Omega\to\mathbb R$; reason: the paper's definition of a continuous process, p.7; same quantities
-- source:
--   Maulen S., Fadili, Attouch, An SDE perspective on stochastic convex optimization, arXiv:2207.02750v1, Theorem A.8, p.35

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology InnerProductSpace

namespace SDEConvexOpt

/-- Theorem A.8 of Maulen S., Fadili, Attouch, arXiv:2207.02750v1, p.35 (cited from [49]): let
`(Mₜ)_{t ≥ 0} : Ω → ℝ` be a continuous martingale such that `sup_{t ≥ 0} 𝔼(|Mₜ|^p) < ∞` for some
`p > 1`. Then there exists a random variable `M∞` such that `𝔼(|M∞|^p) < ∞` and
`lim_{t→∞} Mₜ = M∞` a.s.

**Formalization Note** Time is `ℝ≥0`; `M` is a Mathlib `Martingale` for a filtration `𝓕` with
almost surely continuous paths (the paper's "continuous", p.7). Expectations of `|·|^p` are lower
Lebesgue integrals in `ℝ≥0∞` with a real exponent. `M∞` is measurable. -/
theorem theorem_A_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M ℱ P)
    (hMc : ∀ᵐ ω ∂P, Continuous (fun t => M t ω)) (p : ℝ) (hp : 1 < p)
    (hbdd : (⨆ t : ℝ≥0, ∫⁻ ω, ‖M t ω‖ₑ ^ p ∂P) < ∞) :
    ∃ Minf : Ω → ℝ, Measurable Minf ∧ ∫⁻ ω, ‖Minf ω‖ₑ ^ p ∂P < ∞ ∧
      ∀ᵐ ω ∂P, Tendsto (fun t => M t ω) atTop (𝓝 (Minf ω)) := by sorry

end SDEConvexOpt
