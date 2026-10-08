-- Prove2me | Theorems.Thm_TsayQF_EffQF_proposition_3a
-- name    : TsayQF.EffQF.proposition_3a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:34.854985+00:00
-- url     : https://prove2.me/theorems/20b505db-0956-4248-b8ea-d931d58dea59
-- title:
--   Proposition 3(a), p. 1348 (σ_ε = 0) — for ω < 1 the optimal forecast q*_QF is strictly positive, finite, and the unique solution of (3)
-- statement:
--   Let $p > m > 0$, $u < m$, $s \ge 0$ be the cost data and $u < c < p+s$ the transfer price. Let $\mu$ have law $\nu$ with finite variance and a differentiable, strictly increasing distribution function $\Theta$; with $\sigma_\varepsilon = 0$ demand equals $\mu$. Take a QF contract with $0 \le \omega < 1$ and $\alpha \ge -\omega$. The retailer's forecast objective is
--   $$\pi_R(q) = E_\mu\{G(\mu\perp[q(1-\omega),q(1+\alpha)]\mid\mu)\}, \qquad q \ge 0,$$
--   where the EM builds $q(1+\alpha)$. Write $G'(r\mid\mu)$ for $p+s-c$ if $r<\mu$ and $u-c$ if $r\ge\mu$. Assume
--   $$(1-\omega)(c-u)\Theta(0) < (1+\alpha)(p+s-c)(1-\Theta(0)).$$
--   Then equation (3),
--   $$(1+\alpha)\int_{\mu \ge q(1+\alpha)} G'(q(1+\alpha)\mid\mu)\,d\Theta(\mu) = -(1-\omega)\int_{\mu\le q(1-\omega)} G'(q(1-\omega)\mid\mu)\,d\Theta(\mu),$$
--   has exactly one solution $q > 0$, and a forecast $q \ge 0$ maximizes $\pi_R$ over $[0,\infty)$ if and only if $q > 0$ and $q$ solves (3). In particular the optimal forecast $q^*_{QF}$ exists, is strictly positive and finite, and is the unique solution of (3).
--
--   The left side of (3) is the retailer's expected marginal benefit of raising the forecast (more guaranteed availability), the right side its expected marginal cost (a larger minimum purchase); the condition is the QF analogue of the newsvendor fractile.
--
--   **Formalization Note.** This is the instance $\sigma_\varepsilon = 0$ of the printed statement, whose integration regions read $\mu + z_\varepsilon\sigma_\varepsilon \ge q(1+\alpha)$ and $\mu + z_\varepsilon\sigma_\varepsilon \le q(1-\omega)$. At $\sigma_\varepsilon=0$, $G(\cdot\mid\mu)$ is piecewise linear and $G'$ is taken as its right derivative; its value on the $\Theta$-null diagonal $r = \mu$ does not affect (3), which then reads $(1+\alpha)(p+s-c)(1-\Theta(q(1+\alpha))) = (1-\omega)(c-u)\Theta(q(1-\omega))$. The displayed hypothesis on $\Theta(0)$ is the explicit form of the paper's presumption that $\mu$ is almost certainly nonnegative (under which $\Theta(0) = 0$ and the hypothesis holds); it is exactly what makes the optimal forecast strictly positive. The EM's production is fixed at $q(1+\alpha)$, as §6.1 does after Proposition 2. The price range $u<c<p+s$ generalizes the standing $m<c<p$, because the mission applies the result at $c=\bar c(\psi)$.
-- source:
--   Tsay, The quantity flexibility contract and supplier-customer incentives, Management Science 45(10) (1999), p. 1348, Proposition 3(a), display (3) (instance σ_ε = 0)

import Mathlib
import Definitions.Def_TsayQF_EffQF_Model

open MeasureTheory ProbabilityTheory

namespace TsayQF.EffQF

/-- Proposition 3(a), p. 1348, at `σ_ε = 0`: when `ω < 1`, the retailer's optimal forecast
`q*_QF` is strictly positive and finite, and is the unique solution of (3). -/
theorem proposition_3a (D : Data) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hΘ : StrictMono (cdf ν)) (hΘd : Differentiable ℝ (cdf ν)) (hν : MemLp id 2 ν)
    (c : ℝ) (hcu : D.u < c) (hcp : c < D.p + D.s)
    (α ω : ℝ) (hω0 : 0 ≤ ω) (hω1 : ω < 1) (hα : -ω ≤ α)
    (h0 : (1 - ω) * (c - D.u) * cdf ν 0 < (1 + α) * (D.p + D.s - c) * (1 - cdf ν 0)) :
    let eq3 : ℝ → Prop := fun q =>
      (1 + α) * ∫ μ in Set.Ici (q * (1 + α)), Gderiv D c (q * (1 + α)) μ ∂ν =
        -((1 - ω) * ∫ μ in Set.Iic (q * (1 - ω)), Gderiv D c (q * (1 - ω)) μ ∂ν)
    (∃! q, 0 < q ∧ eq3 q) ∧
      ∀ q, 0 ≤ q → (IsMaxOn (forecastProfit D ν c α ω) (Set.Ici 0) q ↔ (0 < q ∧ eq3 q)) := by sorry

end TsayQF.EffQF
