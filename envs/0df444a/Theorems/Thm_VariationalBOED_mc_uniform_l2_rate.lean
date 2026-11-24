-- Prove2me | Theorems.Thm_VariationalBOED_mc_uniform_l2_rate
-- name    : VariationalBOED.mc_uniform_l2_rate
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T17:39:43.883087+00:00
-- url     : https://prove2.me/theorems/a21d766a-fc5b-47a8-b0cf-8fdf4870bb0e
-- title:
--   Theorem 1 (first assertion): uniform $L^2$ rate $O(N^{-1/2})$ of the Monte Carlo estimator
-- statement:
--   Let $\mathcal X$ be a measurable space and $\Phi$ a convex subset of a finite-dimensional real inner product space. Let $X_1,X_2,\dots$ be i.i.d. random variables with values in $\mathcal X$, and $f:\mathcal X\times\Phi\to\mathbb R$ a measurable function. Put
--
--   $$\mu(\phi)=\mathbb E[f(X_1,\phi)],\qquad\hat\mu_N(\phi)=\frac1N\sum_{n=1}^Nf(X_n,\phi).$$
--
--   If $\sup_{\phi\in\Phi}\|f(X_1,\phi)\|_2<\infty$, where $\|Z\|_2=\sqrt{\mathbb E[Z^2]}$, then
--
--   $$\sup_{\phi\in\Phi}\big\|\hat\mu_N(\phi)-\mu(\phi)\big\|_2=O(N^{-1/2})\qquad(N\to\infty).$$
--
--   This is the Monte Carlo part of the paper's convergence theorem: for any fixed variational parameter, the estimator of a bound converges to the bound at rate $N^{-1/2}$, uniformly in the parameter.
--
--   **Formalization Note** The $L^2$ norm is Mathlib's `eLpNorm _ 2`, with values in $[0,\infty]$. $O(N^{-1/2})$ is stated as a finite constant $C$ with $\sup_\phi\|\hat\mu_N(\phi)-\mu(\phi)\|_2\le C N^{-1/2}$ for all large $N$. Theorem 1's second and third assertions, on stochastic gradient descent, are not formalized; see the mission description.
-- source:
--   Foster, Jankowiak, Bingham, Horsfall, Teh, Rainforth and Goodman, Variational Bayesian Optimal Experimental Design, arXiv:1903.05480v3 (NeurIPS 2019), Section 4, Theorem 1, first assertion, p. 6; proof in Appendix B, eqs. (63)-(68), pp. 16-17

import Mathlib
import Definitions.Def_VariationalBOED_Basic

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology
open scoped ENNReal

namespace VariationalBOED

theorem mc_uniform_l2_rate {Ω S E : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] [MeasurableSpace S]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (Phi : Set E) (hPhi : Convex ℝ Phi)
    (X : ℕ → Ω → S) (hXm : ∀ n, Measurable (X n)) (hXind : iIndepFun X P)
    (hXid : ∀ n, IdentDistrib (X n) (X 0) P P)
    (f : S → Phi → ℝ) (hf : Measurable (Function.uncurry f))
    (hbd : (⨆ φ : Phi, eLpNorm (fun ω => f (X 0 ω) φ) 2 P) < ⊤) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ᶠ N : ℕ in atTop,
      (⨆ φ : Phi, eLpNorm (fun ω => mcEstimate f X N φ ω - mcMean P f X φ) 2 P) ≤
        C * ENNReal.ofReal (1 / Real.sqrt N) := by sorry

end VariationalBOED
