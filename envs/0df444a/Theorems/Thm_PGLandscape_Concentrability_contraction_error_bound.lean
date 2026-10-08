-- Prove2me | Theorems.Thm_PGLandscape_Concentrability_contraction_error_bound
-- name    : PGLandscape.Concentrability.contraction_error_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:29:34.15198+00:00
-- url     : https://prove2.me/theorems/770987fb-cff9-489e-8a77-ad9e0f845b65
-- title:
--   Proof of Theorem 4(c), p. 42 — if T is a γ-contraction in ‖·‖, then (1 − γ)‖J_π − J*‖ ≤ ‖J_π − TJ_π‖
-- statement:
--   Throughout, $(\mathcal S,(\mathcal A_s)_{s\in\mathcal S},g,P,\gamma,\rho)$ is the discounted Markov decision process of §2 of the paper: states in a measurable space $\mathcal S$, feasible action sets $\mathcal A_s$, a bounded measurable per-period cost $g$, a transition kernel $P(\cdot\mid s,a)$, a discount factor $\gamma\in(0,1)$ and an initial distribution $\rho$. For a measurable stationary policy $\pi$, $J_\pi$ is its cost-to-go, $\eta_\pi=(1-\gamma)\sum_{t\ge0}\gamma^t\Pr^\pi_\rho(s_t\in\cdot)$ its discounted state-occupancy measure and $\ell(\pi)=(1-\gamma)\int J_\pi\,d\rho$ its discounted average cost. $T_\pi J(s)=g(s,\pi(s))+\gamma\int J(s')P(ds'\mid s,\pi(s))$ and $TJ(s)=\min_{a\in\mathcal A_s}[g(s,a)+\gamma\int J(s')P(ds'\mid s,a)]$ are the Bellman operators, $\Pi$ is the set of feasible measurable stationary policies, $\pi^*\in\Pi$ is an optimal policy and $J^*=J_{\pi^*}$.
--
--   Let $\pi^*$ be an optimal policy, assume measurable selection (Assumption 2), and let $\|\cdot\|$ be a real-valued functional on functions $\mathcal S\to\mathbb R$ such that
--
--   1. **Subadditivity.** $\|f+g\|\le\|f\|+\|g\|$ for all bounded measurable $f,g$.
--   2. **Contraction.** $\|TJ-TJ'\|\le\gamma\,\|J-J'\|$ for all bounded measurable $J,J'$.
--
--   Then for every $\pi\in\Pi$,
--   $$(1-\gamma)\,\|J_\pi-J^*\|\le\|J_\pi-TJ_\pi\|,\qquad\text{i.e.}\qquad\|J_\pi-J^*\|\le\frac1{1-\gamma}\|J_\pi-TJ_\pi\|.$$
--
--   This is (26) transported to any norm in which $T$ contracts; it is the first step of part (c) of Theorem 4.
--
--   **Formalization Note** The paper's sentence ends with $\|J-TJ^*\|$; since $TJ^*=J^*$ that reading is trivial, and the next display of the proof uses $\|J-TJ\|$, so the latter is stated. "A norm" is encoded only by the property the argument uses, subadditivity on bounded measurable functions, which makes the statement more general. The paper prints $T_\pi$ and $T$ in (3)–(4) without the factor $\gamma$; every later use (Assumption 2, (6), (7), the proofs) has it, and the formalization includes it.
-- source:
--   arXiv:1906.01786v3, App. D.3, proof of part (c) of Theorem 4, first sentence, p. 42

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP

namespace PGLandscape.Concentrability

open MeasureTheory ProbabilityTheory

/-- App. D.3, proof of Theorem 4(c), first sentence, p. 42: if `T` is a contraction with modulus `γ`
in `N` (and `N` is subadditive on bounded measurable functions), then for every `π ∈ Π`,
`(1 − γ) N(J_π − J*) ≤ N(J_π − TJ_π)`, with `J* = J_{π*}`. -/
theorem contraction_error_bound {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (M : PGLandscape.Closure.MDP S A) (πstar : PGLandscape.Closure.MPolicy S A) (hopt : PGLandscape.Closure.IsOptimal M πstar) (hA2 : PGLandscape.Closure.Assumption2 M)
    (N : (S → ℝ) → ℝ)
    (hN_sub : ∀ f g : S → ℝ, (Measurable f ∧ ∃ K : ℝ, ∀ s, |f s| ≤ K) →
      (Measurable g ∧ ∃ K : ℝ, ∀ s, |g s| ≤ K) → N (f + g) ≤ N f + N g)
    (hT : ∀ J J' : S → ℝ, (Measurable J ∧ ∃ K : ℝ, ∀ s, |J s| ≤ K) →
      (Measurable J' ∧ ∃ K : ℝ, ∀ s, |J' s| ≤ K) →
      N (PGLandscape.Closure.bellmanOpt M J - PGLandscape.Closure.bellmanOpt M J') ≤ M.γ * N (J - J'))
    (π : PGLandscape.Closure.MPolicy S A) (hπ : PGLandscape.Closure.IsFeasible M π) :
    (1 - M.γ) * N (fun s => PGLandscape.Closure.costToGo M π s - PGLandscape.Closure.costToGo M πstar s) ≤
      N (fun s => PGLandscape.Closure.costToGo M π s - PGLandscape.Closure.bellmanOpt M (PGLandscape.Closure.costToGo M π) s) := by sorry

end PGLandscape.Concentrability
