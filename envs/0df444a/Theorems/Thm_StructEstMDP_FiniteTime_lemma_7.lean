-- Prove2me | Theorems.Thm_StructEstMDP_FiniteTime_lemma_7
-- name    : StructEstMDP.FiniteTime.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:12:09.825367+00:00
-- url     : https://prove2.me/theorems/5d482bee-4efa-4354-8a45-e92696a62883
-- title:
--   Lemma 7, p. 20 — approximate soft policy iteration: Q_k ≤ Q_{k+½} + 2γε/(1−γ) and ‖Q_θ − Q_{k+½}‖_∞ ≤ γ‖Q_θ − Q_k‖_∞ + 2γε/(1−γ)
-- statement:
--   Let $(\mathcal S,\mathcal A,P)$ be a finite MDP with discount $\gamma\in[0,1)$, $r(\cdot,\cdot;\theta)$ a reward and $\pi$ a policy, and let $Q^\pi_\theta$ be the soft Q-function of $(\theta,\pi)$ and $Q_\theta$ the soft-optimal Q-function. Let $\widehat Q$ satisfy $\|\widehat Q-Q^\pi_\theta\|_\infty\le\varepsilon$, and let $\pi'=\mathrm{softmax}(\widehat Q)$, i.e. $\pi'(a\mid s)\propto e^{\widehat Q(s,a)}$ as in (15). Then
--
--   $$Q^\pi_\theta(s,a)\le Q^{\pi'}_\theta(s,a)+\frac{2\gamma\varepsilon}{1-\gamma}\quad\text{for all }(s,a),\qquad(32)$$
--
--   $$\|Q_\theta-Q^{\pi'}_\theta\|_\infty\le\gamma\|Q_\theta-Q^\pi_\theta\|_\infty+\frac{2\gamma\varepsilon}{1-\gamma}.\qquad(33)$$
--
--   In the paper's notation $\pi=\pi_k$, $\theta=\theta_k$, $Q^\pi_\theta=Q_k$, $\pi'=\pi_{k+1}$ and $Q^{\pi'}_\theta=Q_{k+\frac12}$. (33) is the contraction of the policy-tracking error that drives the lower-level convergence.
--
--   **Formalization Note** The page writes the lemma along the iterates of (15); the Lean states one step for an arbitrary policy and an arbitrary $\varepsilon$-accurate estimate, which is what the lemma asserts at every iteration.
-- source:
--   Zeng, Hong and Garcia, Structural Estimation of Markov Decision Processes in High-Dimensional State Space with Finite-Time Guarantees, arXiv:2210.01282v3, p. 20, Lemma 7, (32)–(33); proof §20, pp. 40–44

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_StructEstMDP_FiniteTime_Setting

open FoundationsML.ReinforcementLearning MeasureTheory

namespace StructEstMDP.FiniteTime

/-- Lemma 7, p. 20: one step of approximate soft policy iteration (15). If `‖Q̂ − Q^π_θ‖_∞ ≤ ε`
and `π' = softmax(Q̂)`, then (32) `Q^π_θ ≤ Q^{π'}_θ + 2γε/(1−γ)` pointwise, and (33)
`‖Q_θ − Q^{π'}_θ‖_∞ ≤ γ ‖Q_θ − Q^π_θ‖_∞ + 2γε/(1−γ)`. -/
theorem lemma_7 {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (γ : ℝ)
    (hP : IsTransitionKernel P) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {p : ℕ} (r : S → A → EuclideanSpace ℝ (Fin p) → ℝ)
    (θ : EuclideanSpace ℝ (Fin p)) (π : S → A → ℝ) (hπ : IsPolicy π)
    (Qhat : S → A → ℝ) (ε : ℝ) (hQ : supNorm (Qhat - softQ P γ r θ π) ≤ ε) :
    (∀ (s : S) (a : A),
        softQ P γ r θ π s a ≤ softQ P γ r θ (softmax Qhat) s a + 2 * γ * ε / (1 - γ)) ∧
      supNorm (optQ P γ r θ - softQ P γ r θ (softmax Qhat)) ≤
        γ * supNorm (optQ P γ r θ - softQ P γ r θ π) + 2 * γ * ε / (1 - γ) := by sorry

end StructEstMDP.FiniteTime
