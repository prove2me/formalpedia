-- Prove2me | Theorems.Thm_TightQLearning_lemma_4
-- name    : TightQLearning.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:31:27.594464+00:00
-- url     : https://prove2.me/theorems/10627a48-9cf0-4b56-a2fc-63383d69d395
-- title:
--   Lemma 4 — $0\le Q_t\le\frac1{1-\gamma}$ and $0\le V_t\le\frac1{1-\gamma}$
-- statement:
--   Let $\gamma\in(0,1)$, let the rewards lie in $[0,1]$, and let $0\le Q_0\le\frac{1}{1-\gamma}$. If $0\le\eta_t\le1$ for $t\le T$, then for all $t\le T$ and on every sample table,
--   $$0\le Q_t\le\frac{1}{1-\gamma}\mathbf 1\qquad\text{and}\qquad0\le V_t\le\frac{1}{1-\gamma}\mathbf 1.$$
--
--   This keeps the iterates in the range of the true Q-function. It yields the crude bound $\|\Delta_t\|_\infty\le\frac1{1-\gamma}$ and the bounds on the martingale differences.
--
--   Differences from the source:
--   - encoding: the state and action spaces are {1,…,|S|} and {1,…,|A|} → finite nonempty types X and A; reason: the instances are the same up to relabelling; |S||A| is Fintype.card X * Fintype.card A
--   - generalization: 0 ≤ η_t ≤ 1 for all t ≥ 0, conclusion for all t ≥ 0 → the same up to an arbitrary horizon T; reason: T arbitrary gives the page's statement; (16a) constrains the rates only up to T
--   - generalization: random samples s_t(s,a) → any table of samples; reason: the page's proof is pathwise; a random table is a special case
-- source:
--   Li, Cai, Chen, Wei & Chi, Is Q-Learning Minimax Optimal? A Tight Sample Complexity Analysis, arXiv:2102.06548v4 (https://arxiv.org/abs/2102.06548v4), Lemma 4, (60), p.20

import Mathlib
import Definitions.Def_TightQLearning_syncQ

open QLearning.Convergence

namespace TightQLearning

/-- Lemma 4, (60) (Li, Cai, Chen, Wei & Chi, arXiv:2102.06548v4, p.20): if `0 ≤ η_t ≤ 1` and
`0 ≤ Q₀ ≤ 1/(1−γ)`, then `0 ≤ Q_t ≤ 1/(1−γ)` and `0 ≤ V_t ≤ 1/(1−γ)`, on every sample path.

**Formalization Note.** Stated for rates known up to a horizon `T`; `T` arbitrary gives the page's
"for all `t ≥ 0`". -/
theorem lemma_4 {X A : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype A] [DecidableEq A] [Nonempty A] (M : FiniteMDP X A)
    (hr : ∀ s a, 0 ≤ M.R s a ∧ M.R s a ≤ 1) (γ : ℝ) (hγ : 0 < γ ∧ γ < 1)
    (η : ℕ → ℝ) (Q0 : X → A → ℝ) (hQ0 : ∀ s a, 0 ≤ Q0 s a ∧ Q0 s a ≤ 1 / (1 - γ))
    (σ : ℕ → X → A → X) (T : ℕ) (hη : ∀ t, t ≤ T → 0 ≤ η t ∧ η t ≤ 1) :
    ∀ t, t ≤ T →
      (∀ s a, 0 ≤ syncQ M γ η Q0 σ t s a ∧ syncQ M γ η Q0 σ t s a ≤ 1 / (1 - γ)) ∧
      (∀ s, 0 ≤ vmax (syncQ M γ η Q0 σ t) s ∧ vmax (syncQ M γ η Q0 σ t) s ≤ 1 / (1 - γ)) := by sorry

end TightQLearning
