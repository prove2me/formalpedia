-- Prove2me | Theorems.Thm_QueueingFundamentals_GG1_mm1_mle
-- name    : QueueingFundamentals.GG1.mm1_mle
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T19:49:10.699465+00:00
-- url     : https://prove2.me/theorems/a8cdd283-dd96-4667-865d-e4d331419bee
-- title:
--   Eq. (6.33) — the maximum-likelihood estimators λ̂ = n_a/t, μ̂ = n_c/t_b for M/M/1
-- statement:
--   An M/M/1 queue is observed for a time $t$, during which it is busy for a time $t_b$ with $0<t_b\le t$, and $n_a>0$ arrivals and $n_c>0$ service completions are recorded. With the initial-state term ignored (the queue in equilibrium), the log-likelihood is $\mathcal L(\lambda,\mu)=-\lambda t-\mu t_b+n_a\ln\lambda+n_c\ln\mu$. Its unique maximizer over $\lambda,\mu>0$ is
--
--   $$
--   \hat\lambda=\frac{n_a}{t},\qquad \hat\mu=\frac{n_c}{t_b}. \tag{6.33}
--   $$
--
--   These are Clarke's maximum-likelihood estimators: the arrival rate is estimated by arrivals per unit of observation time and the service rate by completions per unit of busy time.
--
--   **Formalization Note** The theorem asserts that both estimates are positive and that $\mathcal L(\lambda,\mu)<\mathcal L(\hat\lambda,\hat\mu)$ for every other pair $\lambda,\mu>0$.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.318–319, §6.7, Eq. (6.33) from the log-likelihood (6.32)

import Mathlib
import Definitions.Def_QueueingFundamentals_GG1_Likelihood

namespace QueueingFundamentals.GG1

/-- Eq. (6.33) (p.319): with the `ln Pr{n_0}` term of (6.32) ignored (equilibrium), the
maximum-likelihood estimators of the M/M/1 arrival and service rates are `λ̂ = n_a/t` and
`μ̂ = n_c/t_b`: for observation time `t`, busy time `0 < t_b ≤ t`, and `n_a, n_c > 0` arrivals and
service completions, `(n_a/t, n_c/t_b)` is the unique maximizer of
`𝓛(λ, μ) = −λt − μt_b + n_a ln λ + n_c ln μ` over `λ, μ > 0`. -/
theorem mm1_mle (t tb : ℝ) (htb : 0 < tb) (htbt : tb ≤ t) (na nc : ℕ) (hna : 0 < na)
    (hnc : 0 < nc) :
    0 < (na : ℝ) / t ∧ 0 < (nc : ℝ) / tb ∧
    ∀ lam mu : ℝ, 0 < lam → 0 < mu → (lam, mu) ≠ ((na : ℝ) / t, (nc : ℝ) / tb) →
      mm1LogLik t tb na nc lam mu < mm1LogLik t tb na nc ((na : ℝ) / t) ((nc : ℝ) / tb) := by sorry

end QueueingFundamentals.GG1
