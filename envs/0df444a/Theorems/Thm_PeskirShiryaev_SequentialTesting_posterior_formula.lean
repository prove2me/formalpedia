-- Prove2me | Theorems.Thm_PeskirShiryaev_SequentialTesting_posterior_formula
-- name    : PeskirShiryaev.SequentialTesting.posterior_formula
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:27:46.406778+00:00
-- url     : https://prove2.me/theorems/097f59c8-6cac-48c3-a228-28e735f69844
-- title:
--   Eqs. (21.0.6)–(21.0.8) — likelihood ratio and posterior representation
-- statement:
--   In the Wiener testing experiment, let $L_u=\exp\{(\mu/\sigma^2)(X_u-\mu u/2)\}$ and $\Pi^p_u=pL_u/(1-p+pL_u)$. For every $u\ge0$, $L_u$ is integrable under $P_0$, and for every observation-measurable event $A\in\mathcal F^X_u$,
--   $$P_1(A)=\int_A L_u\,dP_0.$$
--   Moreover, for every $p\in[0,1]$,
--   $$P_p(\theta=1\mid\mathcal F^X_u)=\Pi^p_u\quad P_p\text{-almost surely}.$$
--   This identifies the explicit continuous process with the posterior probability used in Bayesian testing and gives the observation-filtration likelihood ratio.
--
--   **Formalization Note** The Radon–Nikodym identity is expressed by equality of integrals on every event of the observation sigma field. Conditional probability is the conditional expectation of the indicator of $\theta=1$. The book's odds expression is algebraically simplified and extended to deterministic priors $0,1$.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, p. 288 / PDF p. 305, Eqs. (21.0.6)–(21.0.8)

import Definitions.Def_PeskirShiryaev_SequentialTesting_BoundaryClass

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace PeskirShiryaev.SequentialTesting

/-- Equations (21.0.6)-(21.0.8): likelihood and conditional-posterior
identities for the observation filtration. Endpoint priors use the continuous
extension of the displayed odds expression. -/
theorem posterior_formula {Ω : Type*} [MeasurableSpace Ω]
    (E : Model Ω) (C : Parameters) :
    (∀ u : ℝ≥0, Integrable (likelihood E C u) E.P0 ∧
      ∀ A : Set Ω, MeasurableSet[observationSigma E C u] A →
        E.P1.real A = ∫ ω in A, likelihood E C u ω ∂E.P0) ∧
    (∀ p ∈ Icc (0 : ℝ) 1, ∀ u : ℝ≥0,
      (prior E p)[(fun ω => if E.θ ω then (1 : ℝ) else 0) |
        observationSigma E C u] =ᵐ[prior E p] posterior E C p u) := by sorry

end PeskirShiryaev.SequentialTesting
