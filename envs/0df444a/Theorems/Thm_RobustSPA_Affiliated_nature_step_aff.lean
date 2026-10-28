-- Prove2me | Theorems.Thm_RobustSPA_Affiliated_nature_step_aff
-- name    : RobustSPA.Affiliated.nature_step_aff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:47.102389+00:00
-- url     : https://prove2.me/theorems/66acf652-77c7-4761-85f0-6fa75020f467
-- title:
--   Proof of Proposition 2, p. 20 — R(Φ*_n, F) ≤ r*_n + ∫_{r*_n}^1 ((n−1)r*_n/(p−r*_n) − 1 − (n−1)p/(p−r*_n) F^(1)_n(p) + nF^(1)_{n−1}(p)) Φ*_n(p) dp
-- statement:
--   Let $n\ge 2$. Let $r=r^*_n\in(0,1/n)$ satisfy the $r^*$-equation
--   $$(1-r)^{n-1}+\log r+\sum_{k=1}^{n-1}\frac{(1-r)^k}{k}=0 .$$
--   Let $\rho$ be a reserve law whose CDF is $\Phi^*_n$ of Theorem 1, and let $F$ be an exchangeable and affiliated law on $[0,1]^n$. Then the regret of the second-price auction with random reserve $\rho$ against $F$ satisfies
--   $$R_n(\Phi^*_n,F)\ \le\ r^*_n+\int_{r^*_n}^{1}\Big(\frac{(n-1)r^*_n}{p-r^*_n}-1-\frac{(n-1)p}{p-r^*_n}F^{(1)}_n(p)+n\,F^{(1)}_{n-1}(p)\Big)\Phi^*_n(p)\,dp .$$
--
--   This is the bound obtained in the proof of Proposition 2. It comes from the regret formula of Proposition 1, the order-statistic identity (David–Nagaraja 5.3.2) and the differential equation (ODE-$\Phi$) satisfied by $\Phi^*_n$. It leaves only the CDFs of maxima in the integrand, which Lemma 1 and a pointwise maximization then bound by the i.i.d. isorevenue value.
--
--   **Formalization Note.** "$r^*_n$ and $\Phi^*_n$ as given by Theorem 1" is stated as hypotheses: $r$ solves the $r^*$-equation in $(0,1/n)$, and $\rho$ has CDF $\Phi^*_n$ (Theorem 1 is the goal of mission I and cannot be imported). $R_n(\Phi^*_n,F)$ is the regret (2) of $\mathrm{SPA}(\rho)$. On $(r^*_n,1]$ the integrand is bounded, since $\Phi^*_n(p)$ vanishes linearly at $r^*_n$, so the interval integral is a genuine one.
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, p. 20, proof of Proposition 2, second line of the display after (ODE-Φ)

import Mathlib
import Definitions.Def_RobustSPA_Affiliated_Setting

namespace RobustSPA.Affiliated

open MeasureTheory RobustSPA.IID

theorem nature_step_aff (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) (1 / (n : ℝ)))
    (hrEq : rEq n r = 0) (ρ : ProbabilityMeasure ℝ) (hρ : ∀ t, cdfOf ρ t = PhiStar n r t)
    (μ : Measure (Fin n → ℝ)) (hμ : μ ∈ Faff n) :
    regret (SPA (ρ : Measure ℝ)) μ ≤
      r + ∫ p in r..1, (((n : ℝ) - 1) * r / (p - r) - 1 - ((n : ℝ) - 1) * p / (p - r) * F1 μ p +
        (n : ℝ) * F1k (n - 1) μ p) * PhiStar n r p := by sorry

end RobustSPA.Affiliated
