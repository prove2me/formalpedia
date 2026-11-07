-- Prove2me | Theorems.Thm_PrettyGoodShadow_eq_26_laplace
-- name    : PrettyGoodShadow.eq_26_laplace
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:25:46.854361+00:00
-- url     : https://prove2.me/theorems/e116845f-6cb6-41e4-a9cb-3287449803b1
-- title:
--   Eq. (26) — the Laplace estimator has risk at most $\log\frac{m+2}{m+1}$ ([MG22])
-- statement:
--   Let $z_1,\dots,z_m\sim\mathrm{Ber}(\theta)$ and let $\hat\theta_m=(z_1+\dots+z_m+1)/(m+2)$ be the Laplace estimator. For every $\theta\in[0,1]$,
--
--   $$
--   \mathbb E\big[D(\mathrm{Ber}(\theta)\|\mathrm{Ber}(\hat\theta_m))\big]\le\log\frac{m+2}{m+1},
--   $$
--
--   and the same bound holds after averaging over a random $\theta$ on $[0,1]$. The source cites this from [MG22, Proposition 4], and it is the one-step inequality behind Lemma 4.13.
--
--   **Formalization Note** The random $\theta$ is a probability measure on $\mathbb R$ carried by $[0,1]$. Integrability of the risk is part of the statement. Natural logarithm.
--
--   Differences from the source:
--   - encoding: θ a random variable on [0,1], expectation over θ → a probability measure μ on ℝ carried by [0,1], with integrability as a clause; reason: the law of θ determines the expectation; the clause rules out a junk integral
-- source:
--   Grewal, Pelecanos, Spilecki, Tang, Wright, Pretty good shadow tomography, arXiv:2610.06781 (sha256 bd055b7d…), eq. (26), p.27, citing [MG22, Proposition 4]

import Mathlib
import Definitions.Def_PrettyGoodShadow_laplaceRisk

open MeasureTheory

namespace PrettyGoodShadow

/-- **Eq. (26), the Laplace estimator** ([MG22, Proposition 4], cited in arXiv:2610.06781, sha256 bd055b7d…, p.27).
After `m` samples `z_1, …, z_m ∼ Ber(θ)`, the Laplace estimator `θ̂_m = (z_1 + … + z_m + 1)/(m + 2)` satisfies
`E[D(Ber(θ) ∥ Ber(θ̂_m))] ≤ log((m + 2)/(m + 1))`, both for fixed `θ` and, by averaging, for random `θ`.

**Formalization Note** Random `θ` is a probability measure `μ` on `ℝ` carried by `[0, 1]`. Integrability of the
risk is part of the statement, so the second clause cannot come from a junk integral. `m = 0` is included, as on
the page. -/
theorem eq_26_laplace (m : ℕ) :
    (∀ θ ∈ Set.Icc (0 : ℝ) 1, laplaceRisk m θ ≤ Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1))) ∧
    (∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], (∀ᵐ θ ∂μ, θ ∈ Set.Icc (0 : ℝ) 1) →
      Integrable (laplaceRisk m) μ ∧
        ∫ θ, laplaceRisk m θ ∂μ ≤ Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1))) := by sorry

end PrettyGoodShadow
