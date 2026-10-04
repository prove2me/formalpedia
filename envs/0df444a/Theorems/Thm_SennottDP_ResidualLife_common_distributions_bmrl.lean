-- Prove2me | Theorems.Thm_SennottDP_ResidualLife_common_distributions_bmrl
-- name    : SennottDP.ResidualLife.common_distributions_bmrl
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T10:36:03.91481+00:00
-- url     : https://prove2.me/theorems/7d6160bc-b466-42b4-a22a-40085d8e68ee
-- title:
--   Proposition 9.2.6 — the geometric, negative binomial and truncated Poisson distributions are BMRL
-- statement:
--   The following distributions on $\{1,2,\dots\}$ have bounded mean residual lifetimes (BMRL), i.e. for each there is a finite constant $U$ with $E[Y_s] \le U$ for every $s \ge 0$ with $P(Y > s) > 0$:
--
--   1. the geometric distribution $\mathrm{geo}(\mu)$, $P(Y=y) = \mu(1-\mu)^{y-1}$, $y \ge 1$, for every $0 < \mu < 1$;
--   2. the negative binomial distribution $\mathrm{neg\,bin}(\mu,r)$ of the number of trials to the $r$-th success, $P(Y=y) = \binom{y-1}{r-1}\mu^r(1-\mu)^{y-r}$, $y \ge r$, for every $0<\mu<1$ and $r \ge 2$;
--   3. the truncated Poisson distribution $\mathrm{trun\,Pois}(\lambda)$, $P(Y = y) = \dfrac{e^{-\lambda}}{1-e^{-\lambda}}\dfrac{\lambda^y}{y!}$, $y \ge 1$, for every $\lambda > 0$.
--
--   Together with Proposition 9.2.5 this shows that these common unbounded service distributions have finite moments of all orders and fit the average cost framework of Chapter 9.
--
--   **Formalization Note** The three distributions are the functions of the definition `Distributions`; BMRL is the definition `IsBMRLDist` (existence of a finite bound $U$). The bound may depend on the parameters $\mu$, $r$, $\lambda$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 205–206, Proposition 9.2.6

import Mathlib
import Definitions.Def_SennottDP_ResidualLife_MSDist
import Definitions.Def_SennottDP_ResidualLife_Distributions

open scoped ENNReal NNReal

namespace SennottDP.ResidualLife

/-- Sennott (1999), Proposition 9.2.6, pp. 205–206: the geometric distribution `geo(μ)`
(`0 < μ < 1`), the negative binomial distribution `neg bin(μ, r)` (`0 < μ < 1`, `r ≥ 2`) and the
truncated Poisson distribution `trun Pois(λ)` (`λ > 0`) are BMRL. -/
theorem common_distributions_bmrl :
    (∀ μ : ℝ, 0 < μ → μ < 1 → IsBMRLDist (geomTrials μ)) ∧
    (∀ μ : ℝ, 0 < μ → μ < 1 → ∀ r : ℕ, 2 ≤ r → IsBMRLDist (negBinTrials μ r)) ∧
    (∀ lam : ℝ, 0 < lam → IsBMRLDist (truncPoisson lam)) := by sorry

end SennottDP.ResidualLife
