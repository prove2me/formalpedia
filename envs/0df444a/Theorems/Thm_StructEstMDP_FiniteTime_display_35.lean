-- Prove2me | Theorems.Thm_StructEstMDP_FiniteTime_display_35
-- name    : StructEstMDP.FiniteTime.display_35
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:12:11.000988+00:00
-- url     : https://prove2.me/theorems/43d08efb-553f-4003-8143-88cdbc32966c
-- title:
--   Display (35), p. 20 — ‖log softmax(Q̂) − log π_θ‖_∞ ≤ 2‖Q̂ − Q_θ‖_∞ ≤ 2ε + 2‖Q − Q_θ‖_∞
-- statement:
--   Let $Q_\theta$ be the soft-optimal Q-function of a finite MDP with reward parameter $\theta$, and $\pi_\theta=\mathrm{softmax}(Q_\theta)$ the soft-optimal policy. For all $\widehat Q,Q:\mathcal S\times\mathcal A\to\mathbb R$ with $\|\widehat Q-Q\|_\infty\le\varepsilon$,
--
--   $$\big\|\log\mathrm{softmax}(\widehat Q)-\log\pi_\theta\big\|_\infty\le2\|\widehat Q-Q_\theta\|_\infty\le2\varepsilon+2\|Q-Q_\theta\|_\infty,$$
--
--   where $\|\log\pi-\log\pi'\|_\infty=\max_{s,a}|\log\pi(a\mid s)-\log\pi'(a\mid s)|$.
--
--   Applied to $\widehat Q=\widehat Q_k$ and $Q=Q_k$ this is (35): it converts the Q-function tracking error into the policy error of (21a).
--
--   **Formalization Note** Both policies are softmax policies, hence strictly positive, so the logarithms are genuine. The first inequality holds for $Q_\theta$ replaced by any function; it is stated with $Q_\theta$ as on the page.
-- source:
--   Zeng, Hong and Garcia, Structural Estimation of Markov Decision Processes in High-Dimensional State Space with Finite-Time Guarantees, arXiv:2210.01282v3, p. 20, display (35), proof of Theorem 1

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_StructEstMDP_FiniteTime_Setting

open FoundationsML.ReinforcementLearning MeasureTheory

namespace StructEstMDP.FiniteTime

/-- Display (35), p. 20: for the softmax policies `softmax(Q̂)` and `π_θ = softmax(Q_θ)`,
`‖log softmax(Q̂) − log π_θ‖_∞ ≤ 2‖Q̂ − Q_θ‖_∞`, and if `‖Q̂ − Q‖_∞ ≤ ε` then
`2‖Q̂ − Q_θ‖_∞ ≤ 2ε + 2‖Q − Q_θ‖_∞`. -/
theorem display_35 {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (γ : ℝ) {p : ℕ} (r : S → A → EuclideanSpace ℝ (Fin p) → ℝ)
    (θ : EuclideanSpace ℝ (Fin p)) (Qhat Q : S → A → ℝ) (ε : ℝ)
    (hQ : supNorm (Qhat - Q) ≤ ε) :
    supNorm (fun s a => Real.log (softmax Qhat s a) - Real.log (optPolicy P γ r θ s a)) ≤
        2 * supNorm (Qhat - optQ P γ r θ) ∧
      2 * supNorm (Qhat - optQ P γ r θ) ≤ 2 * ε + 2 * supNorm (Q - optQ P γ r θ) := by sorry

end StructEstMDP.FiniteTime
