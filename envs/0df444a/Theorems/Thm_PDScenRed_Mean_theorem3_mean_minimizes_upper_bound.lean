-- Prove2me | Theorems.Thm_PDScenRed_Mean_theorem3_mean_minimizes_upper_bound
-- name    : PDScenRed.Mean.theorem3_mean_minimizes_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:02:42.454053+00:00
-- url     : https://prove2.me/theorems/6e538b5b-3f52-4841-bddd-cc0bb83a16b3
-- title:
--   Theorem 3, p. 24 — under Assumption 5, the mean minimizes the one-scenario upper bound and Wasserstein objectives
-- statement:
--   Let $\mathcal Z = \{z\in\mathbb R^d_+ : Pz\le q\}$ be a nonempty bounded polytope, consider the cost $c(z;\xi)=\max\{z'\xi,0\}$, and let $z^*:\mathbb R^d\to\mathbb R^d$ be a measurable selection of minimizers, $z^*(\xi)\in\arg\min_{z\in\mathcal Z} z'\xi$ for every $\xi$. Put $\mathcal U=\{\xi:\min_{z\in\mathcal Z} z'\xi<0\}$. Let $\xi$ be a random vector in $\mathbb R^d$ with law $\mu$, and suppose Assumption 5:
--
--   1. (5a) $\xi$ has a continuous distribution on $\mathcal U$ and density $0$ elsewhere: $\mu$ is absolutely continuous with respect to Lebesgue measure and $\mu(\mathbb R^d\setminus\mathcal U)=0$;
--   2. (5b) the mean $\bar\xi=\mathbb E[\xi]$ is finite and $z^*(\bar\xi)'\bar\xi>0$;
--   3. (5c) the law of $\xi$ is symmetric about $\bar\xi$: $\xi$ and $2\bar\xi-\xi$ are equal in distribution.
--
--   With the loss $L(\xi,\zeta)=\max\{\max_{z\in\mathcal Z} z'(\xi-2\zeta),0\}+2\max\{z^*(\xi)'\zeta,0\}$, the mean minimizes the upper-bound objective for a single reduced scenario ($m=1$):
--
--   $$\mathbb E\big[L(\xi,\bar\xi)\big] \;\le\; \mathbb E\big[L(\xi,\zeta)\big]\quad\text{and}\quad \int\|\xi-\bar\xi\|_2^2\,d\mu\;\le\;\int\|\xi-\zeta\|_2^2\,d\mu\qquad\text{for every }\zeta\in\mathbb R^d.$$
--
--   The theorem says that, in the simplest case, the problem-dependent scenario reduction of the paper, computed through its convex upper bound (16), returns the same single scenario as Wasserstein scenario reduction: the mean.
--
--   **Formalization Note**
--   1. The goal is stated on $\mathbb E[L(\xi,\zeta)]$, the form of the objective in the first display of the proof. For this cost ($k=2$, $A_1=I$, $A_2=0$ in (15)), the optimal value of the per-point linear programme of (16) in $(\lambda,\theta,\gamma)$ equals $L(\xi^i,\zeta)$ by LP duality (last sentence of the proof of Proposition 3); Theorem 3 is the population ($m=1$, expectation instead of a finite sum) version.
--   2. "The solution is simply the mean" is read as "$\bar\xi$ is a minimizer", which is what the proof concludes; uniqueness is not claimed.
--   3. The Wasserstein clause uses the extended nonnegative integral of squared Euclidean distance, so the statement has no added second-moment hypothesis. If the second moment is infinite, all one-scenario costs are infinite; if it is finite, the displayed inequality states the usual Wasserstein solution. Taking the square root as in (4) preserves minimizers.
--   4. $z^*$ is an arbitrary measurable selection; measurability is needed for $\mathbb E[z^*(\xi)]$ and is not on the page. Assumption 5a is two hypotheses; full support is not assumed (it would contradict $\mu(\mathbb R^d\setminus\mathcal U)=0$). The paper's $\mathcal Z$ is nonempty and compact (§1); the polytope is closed, so boundedness is the stated hypothesis. Under these hypotheses $\xi\mapsto L(\xi,\zeta)$ is integrable for every $\zeta$, so both sides are genuine expectations.
-- source:
--   Bertsimas & Mundru, Optimization-based Scenario Reduction for Data-Driven Two-stage Stochastic Optimization, author manuscript (MIT DSpace), p. 24, Theorem 3 and Assumption 5; proof pp. 24–25; problem (16), p. 22

import Mathlib
import Definitions.Def_PDScenRed_Mean_Setting
open scoped InnerProductSpace
open MeasureTheory

namespace PDScenRed.Mean

theorem theorem3_mean_minimizes_upper_bound {d r : ℕ}
    (P : Matrix (Fin r) (Fin d) ℝ) (qv : Fin r → ℝ)
    (hne : (polytope P qv).Nonempty) (hbdd : Bornology.IsBounded (polytope P qv))
    (zsel : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hsel : ∀ ξ, zsel ξ ∈ SmartPTO.Fisher.Wstar (polytope P qv) ξ) (hmeas : Measurable zsel)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (hac : μ ≪ volume) (hU : μ ((Uset (polytope P qv))ᶜ) = 0)
    (hint : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => ξ) μ)
    (hpos : 0 < ⟪zsel (∫ ξ, ξ ∂μ), ∫ ξ, ξ ∂μ⟫_ℝ)
    (hsym : SmartPTO.Fisher.CentrallySymmetric μ) :
    ∀ ζ : EuclideanSpace ℝ (Fin d),
      upperBoundObj (polytope P qv) zsel μ (∫ ξ, ξ ∂μ) ≤
        upperBoundObj (polytope P qv) zsel μ ζ ∧
      wassersteinOneObj μ (∫ ξ, ξ ∂μ) ≤ wassersteinOneObj μ ζ := by sorry

end PDScenRed.Mean
