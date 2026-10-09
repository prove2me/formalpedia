-- Prove2me | Theorems.Thm_RobustSAA_Univariate_theorem_5
-- name    : RobustSAA.Univariate.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:03.483969+00:00
-- url     : https://prove2.me/theorems/7bf129e5-e2cd-40ef-ad8d-be70d2cf45fe
-- title:
--   Theorem 5, p. 14 — the KS, Kuiper, CvM, Watson and AD tests with O(N^(−1/2)) thresholds are uniformly consistent
-- statement:
--   Let the data $\xi^1,\xi^2,\dots$ be iid from a continuous (atomless) distribution $F$ on $\mathbb R$. For thresholds $\tau_N$ with $\tau_N\le q/\sqrt N$ for some constant $q$ and all $N\ge1$, consider the confidence regions
--
--   $$\mathcal F^{S}_N=\{F_0:\ S_N(F_0;\xi^1,\dots,\xi^N)\le\tau_N\},\qquad S_N\in\{D_N,V_N,W_N,U_N,A_N\},$$
--
--   of the Kolmogorov–Smirnov, Kuiper, Cramér–von Mises, Watson and Anderson–Darling statistics (8). Then each of the five tests is **uniformly consistent**: almost surely, every sequence of distributions $F_N$ that does not converge weakly to $F$ satisfies
--
--   $$F_N\notin\mathcal F^{S}_N\quad\text{for infinitely many }N.$$
--
--   By Theorem 2 of the paper, uniform consistency is exactly what makes Robust SAA built on these confidence regions converge in objective, optimal value and optimal solutions for every admissible cost.
--
--   **Formalization Note** The paper's threshold $Q_{S_N}(\alpha)$ enters only through its rate $O(N^{-1/2})$ (pp. 9, 38–39), which is the hypothesis here; one sequence $\tau$ is quantified universally, so each test may use its own threshold. Distributions range over all of $\mathbb R$; a support $[\underline\xi,\overline\xi]$ with infinite endpoints is this case, and finite endpoints are a special case. The data law is required to be atomless, the standing assumption of §3.2 ("ξ is a univariate continuous random variable"); the paper's proof does not use it. $A_N$ is $+\infty$ when some $F_0(\xi^{(i)})\in\{0,1\}$. The paper's argument for the Watson test (p. 39) asserts an $O(1/N)$ bound that fails when $D'_N(F_0)$ is large; the Watson clause is believed true but its proof needs a different argument.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, Theorem 5, p. 14; proof §10.7, pp. 38–39

import Mathlib
import Definitions.Def_RobustSAA_Univariate_Setting

namespace RobustSAA.Univariate

open Filter MeasureTheory

/-- Theorem 5, p. 14: for univariate data from a continuous law, the KS, Kuiper, CvM, Watson and
AD tests with thresholds `τ_N = O(N^{−1/2})` are uniformly consistent. -/
theorem theorem_5 (τ : ℕ → ℝ) (hτ : ThresholdRate τ) :
    IsUniformlyConsistent IsContinuousLaw (ksRegion τ) ∧
    IsUniformlyConsistent IsContinuousLaw (kuiperRegion τ) ∧
    IsUniformlyConsistent IsContinuousLaw (cvmRegion τ) ∧
    IsUniformlyConsistent IsContinuousLaw (watsonRegion τ) ∧
    IsUniformlyConsistent IsContinuousLaw (adRegion τ) := by sorry

end RobustSAA.Univariate
