-- Prove2me | Theorems.Thm_RegretBandits_Stochastic_kl_bernoulli_bounds
-- name    : RegretBandits.Stochastic.kl_bernoulli_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:19:49.290587+00:00
-- url     : https://prove2.me/theorems/d50919cc-064e-4a04-92b3-4c0379254a61
-- title:
--   Eq. (2.8) — $2(p-q)^2\le\mathrm{kl}(p,q)\le(p-q)^2/(q(1-q))$
-- statement:
--   For $p\in[0,1]$ and $q\in(0,1)$, the Kullback–Leibler divergence between Bernoulli distributions of parameters $p$ and $q$ satisfies
--   $$2(p-q)^2\le\mathrm{kl}(p,q)\le\frac{(p-q)^2}{q(1-q)}.$$
--   The left inequality is Pinsker's inequality.
--
--   With (2.8), the constant $\sum_i\Delta_i/\mathrm{kl}(\mu_i,\mu^*)$ of the lower bound (Theorem 2.2) can be compared with the constant $\sum_i 2\alpha/\Delta_i$ of the upper bound (2.4).
--
--   **Formalization Note.** The book states (2.8) for $p,q\in[0,1]$. At $q\in\{0,1\}$ the right side has a zero denominator and $\mathrm{kl}$ may be $+\infty$, so $q\in(0,1)$ is assumed.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 13, Eq. (2.8)

import Mathlib
import Definitions.Def_RegretBandits_Stochastic_klBernoulli

namespace RegretBandits.Stochastic

/-- Eq. (2.8) of Bubeck and Cesa-Bianchi (arXiv:1204.5721v2, p. 13): for `p ∈ [0, 1]` and
`q ∈ (0, 1)`, `2(p - q)² ≤ kl(p, q) ≤ (p - q)² / (q(1 - q))`. -/
theorem kl_bernoulli_bounds (p q : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    2 * (p - q) ^ 2 ≤ klBern p q ∧ klBern p q ≤ (p - q) ^ 2 / (q * (1 - q)) := by sorry

end RegretBandits.Stochastic
