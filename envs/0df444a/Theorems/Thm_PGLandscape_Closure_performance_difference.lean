-- Prove2me | Theorems.Thm_PGLandscape_Closure_performance_difference
-- name    : PGLandscape.Closure.performance_difference
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:27:32.120735+00:00
-- url     : https://prove2.me/theorems/e5621679-cdfe-4120-b9cb-81adce388855
-- title:
--   (29), App. D.1, p. 39 — performance difference: ℓ(π) − ℓ(π̄) = ∫ [T_π J_π̄ − J_π̄] dη_π
-- statement:
--   Let $(\mathcal S,(\mathcal A_s),g,P,\gamma,\rho)$ be a discounted Markov decision process, and let $\pi,\bar\pi$ be measurable stationary policies with cost-to-go functions $J_\pi,J_{\bar\pi}$, discounted average costs $\ell(\pi) = (1-\gamma)\int J_\pi\,d\rho$, $\ell(\bar\pi)$, and discounted state-occupancy measure $\eta_\pi$ of $\pi$. Then
--   $$\ell(\pi)-\ell(\bar\pi) = \int\big[T_\pi J_{\bar\pi}-J_{\bar\pi}\big]\,d\eta_\pi ,$$
--   where $(T_\pi J)(s) = g(s,\pi(s))+\gamma\int J\,dP(\cdot\mid s,\pi(s))$.
--
--   This is the performance difference lemma in the normalized-cost form. It expresses the gap between two policies through the one-step improvement of $\pi$ over $\bar\pi$'s cost-to-go, averaged under $\pi$'s own occupancy measure, and is the identity behind the policy gradient theorem and the on-average Bellman equation.
--
--   **Formalization Note** The page's middle member, the expectation $(1-\gamma)E^\pi_\rho[\sum_t\gamma^t(T_\pi J_{\bar\pi}(s_t)-J_{\bar\pi}(s_t))]$ over the controlled chain, has no object in this formalization and is left out; the statement is the equality of the outer members. It is stated for all measurable policies, feasible or not, which the cost and kernel being defined on all of $\mathcal S\times\mathcal A$ makes meaningful.
-- source:
--   arXiv:1906.01786v3, (29), App. D.1, p. 39

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP

namespace PGLandscape.Closure

open MeasureTheory ProbabilityTheory

theorem performance_difference {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (M : MDP S A) (π πbar : MPolicy S A) :
    loss M π - loss M πbar =
      ∫ s, (bellmanPi M π.1 (costToGo M πbar) s - costToGo M πbar s) ∂(occupancy M π) := by sorry

end PGLandscape.Closure
