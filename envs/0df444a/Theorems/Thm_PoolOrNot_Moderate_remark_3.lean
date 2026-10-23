-- Prove2me | Theorems.Thm_PoolOrNot_Moderate_remark_3
-- name    : PoolOrNot.Moderate.remark_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:48.656435+00:00
-- url     : https://prove2.me/theorems/0129eb22-0459-4999-b685-440fd0d2d322
-- title:
--   Remark 3, p. 10 — under (1): 0 < q < 1, ⌊q⌋ = 0, q̄ = 1, r = q, and p = 1 − (1 − r)/ρ < 1
-- statement:
--   Let $\mu, \theta > 0$ and assume the moderate overloading condition (1):
--   $$1 < \rho < 1 + \frac{\theta}{\mu}.$$
--   Then by (18), $0 < q < 1$, $\lfloor q \rfloor = 0$, $\bar q = 1$ and $r = q$, and the parameter $p$ of Theorem 4 satisfies
--   $$p = \frac{r(\mu + \theta)}{\rho\mu} = 1 - \frac{1 - r}{\rho} < 1.$$
--
--   Since $T_a(0) = 0$, the limit of Theorem 4 is $W = \chi\,T_a(1)$ in this regime: a fraction about $1 - p > 0$ of customers enters service without delay.
--
--   **Formalization Note** Only the arithmetic content of the remark is formalized; its "about" sentences are the content of Theorems 4 and 5.
-- source:
--   Cao, He, Huang & Liu, To Pool or Not to Pool: Queueing Design for Large-Scale Service Systems, Operations Research, Articles in Advance (2020), doi:10.1287/opre.2019.1976, p. 10 (PDF 11), Remark 3; condition (1), p. 3 (PDF 4)

import Mathlib
import Definitions.Def_PoolOrNot_Moderate_Chain

namespace PoolOrNot.Moderate

/-- **Remark 3**, p. 10. Under the moderate overloading condition (1), `1 < ρ < 1 + θ/μ`:
`0 < q < 1`, `⌊q⌋ = 0`, `q̄ = 1`, `r = q`, and the delay probability of Theorem 4,
`p = r(μ + θ)/(ρμ) = 1 − (1 − r)/ρ`, is strictly less than `1`. -/
theorem remark_3 (μ θ ρ : ℝ) (hμ : 0 < μ) (hθ : 0 < θ) (hρ1 : 1 < ρ) (hρ2 : ρ < 1 + θ / μ) :
    0 < qOf ρ μ θ ∧ qOf ρ μ θ < 1 ∧ ⌊qOf ρ μ θ⌋₊ = 0 ∧ qBar ρ μ θ = 1 ∧
    rOf ρ μ θ = qOf ρ μ θ ∧
    pMix ρ μ θ = rOf ρ μ θ * (μ + θ) / (ρ * μ) ∧
    rOf ρ μ θ * (μ + θ) / (ρ * μ) = 1 - (1 - rOf ρ μ θ) / ρ ∧
    rOf ρ μ θ * (μ + θ) / (ρ * μ) < 1 := by sorry

end PoolOrNot.Moderate
