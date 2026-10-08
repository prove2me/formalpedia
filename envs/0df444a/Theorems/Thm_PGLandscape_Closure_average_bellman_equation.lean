-- Prove2me | Theorems.Thm_PGLandscape_Closure_average_bellman_equation
-- name    : PGLandscape.Closure.average_bellman_equation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:27:22.130978+00:00
-- url     : https://prove2.me/theorems/522881f1-d7c6-4aa8-bed5-5c58b707035d
-- title:
--   Lemma 8, p. 15 — on average Bellman equation: for π ∈ Π, ℓ(π) = ℓ(π*) ⟺ ∫ (J_π − TJ_π) dρ = 0
-- statement:
--   Let $(\mathcal S,(\mathcal A_s),g,P,\gamma,\rho)$ be a discounted Markov decision process with an optimal policy $\pi^*$, and suppose Assumption 1 ($\eta_{\pi^*}\ll\rho$) and Assumption 2 (measurable selection) hold. Then for every feasible measurable stationary policy $\pi\in\Pi$,
--   $$\ell(\pi) = \ell(\pi^*)\quad\Longleftrightarrow\quad\int\big(J_\pi-TJ_\pi\big)\,d\rho = 0 .$$
--
--   The right-hand side is the average Bellman error of $\pi$ under the initial distribution. The lemma says that, under an exploratory initial distribution, a policy is optimal for the average cost exactly when its cost-to-go satisfies Bellman's equation on average.
--
--   **Formalization Note** Assumptions 1 and 2 are standing assumptions of §2. Assumption 2 also makes $TJ_\pi$ measurable, so that the integral is the genuine one. $\pi^*$ enters through the hypothesis that it is an optimal policy ($J_{\pi^*}\le J_\pi$ pointwise for every $\pi\in\Pi$). $T$ carries the factor $\gamma$ omitted in the printed (4).
-- source:
--   arXiv:1906.01786v3, Lemma 8, p. 15 (proof pp. 39–40)

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP

namespace PGLandscape.Closure

open MeasureTheory ProbabilityTheory

theorem average_bellman_equation {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (M : MDP S A) (πstar : MPolicy S A) (hopt : IsOptimal M πstar)
    (hA1 : Assumption1 M πstar) (hA2 : Assumption2 M) (π : MPolicy S A) (hπ : IsFeasible M π) :
    loss M π = loss M πstar ↔
      ∫ s, (costToGo M π s - bellmanOpt M (costToGo M π) s) ∂M.ρ = 0 := by sorry

end PGLandscape.Closure
