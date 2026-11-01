-- Prove2me | Theorems.Thm_TightQLearning_eq_34_35
-- name    : TightQLearning.eq_34_35
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:32:53.806993+00:00
-- url     : https://prove2.me/theorems/8c4e3213-9309-414d-8990-7c7ad2f90362
-- title:
--   (34)–(35) — the two-sided recursion for $\Delta_t$ and its expansion
-- statement:
--   Let $\gamma\in(0,1)$, let the rewards lie in $[0,1]$, let $\Delta_t=Q_t-Q^\star$, let $\pi_i$ be a greedy selection of $Q_i$, and let $\pi^\star$ be a deterministic policy with $Q^{\pi^\star}=Q^\star$. Write $(P_i-P)V$ for the function $(s,a)\mapsto V(s_i(s,a))-\sum_{s'}P(s'\mid s,a)V(s')$. On every sample table, for $1\le t\le T$, entrywise,
--   $$\Delta_t\le(1-\eta_t)\Delta_{t-1}+\eta_t\gamma\big\{P^{\pi_{t-1}}\Delta_{t-1}+(P_t-P)V_{t-1}\big\},$$
--   $$\Delta_t\ge(1-\eta_t)\Delta_{t-1}+\eta_t\gamma\big\{P^{\pi^\star}\Delta_{t-1}+(P_t-P)V_{t-1}\big\},$$
--   and, with the weights $\eta_i^{(t)}$ of (36),
--   $$\Delta_t\le\eta_0^{(t)}\Delta_0+\sum_{i=1}^t\eta_i^{(t)}\gamma\big\{P^{\pi_{i-1}}\Delta_{i-1}+(P_i-P)V_{i-1}\big\},$$
--   $$\Delta_t\ge\eta_0^{(t)}\Delta_0+\sum_{i=1}^t\eta_i^{(t)}\gamma\big\{P^{\pi^\star}\Delta_{i-1}+(P_i-P)V_{i-1}\big\}.$$
--
--   This decomposition is the starting point of the analysis: it keeps the operators $P^{\pi_i}$ instead of bounding them crudely, and that is what removes one factor of the effective horizon.
--
--   Differences from the source:
--   - encoding: the state and action spaces are {1,…,|S|} and {1,…,|A|} → finite nonempty types X and A; reason: the instances are the same up to relabelling; |S||A| is Fintype.card X * Fintype.card A
--   - encoding: V^π and Q^π are expectations along a trajectory → the published PolicyValue series, with QFunction for the first step; reason: the series computes the expectation term by term; Q^π is r + γPV^π, the trajectory with a₀ fixed
--   - generalization: π_t picks the smallest maximizing index (27) → any greedy selection; reason: (27) is one such selection
--   - generalization: η_t ∈ (0,1] → 0 ≤ η_t ≤ 1 up to the horizon T; reason: the proof needs only this range, and (0,1] is contained in it
--   - generalization: the deterministic optimal policy π⋆ → any deterministic π⋆ with Q^{π⋆} = Q⋆; reason: the paper's π⋆ is one such policy
--   - generalization: random samples s_t(s,a) → any table of samples; reason: both inequalities are pathwise on the page
-- source:
--   Li, Cai, Chen, Wei & Chi, Is Q-Learning Minimax Optimal? A Tight Sample Complexity Analysis, arXiv:2102.06548v4 (https://arxiv.org/abs/2102.06548v4), (34)–(35), p.13

import Mathlib
import Definitions.Def_TightQLearning_syncQ
import Definitions.Def_TightQLearning_qStar
import Definitions.Def_TightQLearning_detPolicy
import Definitions.Def_TightQLearning_IsGreedy
import Definitions.Def_TightQLearning_PiOp
import Definitions.Def_TightQLearning_weight

open QLearning.Convergence

namespace TightQLearning

/-- The two-sided recursion (34) and its expansion (35) (Li, Cai, Chen, Wei & Chi,
arXiv:2102.06548v4, p.13), on every sample path, entrywise, for `Δ_t = Q_t − Q⋆`, with `π_i` any
greedy selection of `Q_i` and `π⋆` any deterministic policy with `Q^{π⋆} = Q⋆`. The term
`(P_i − P)V_{i−1}` at `(s,a)` is `V_{i−1}(s_i(s,a)) − ∑_{s'} P(s'|s,a) V_{i−1}(s')`, see (29). -/
theorem eq_34_35 {X A : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype A] [DecidableEq A] [Nonempty A] (M : FiniteMDP X A)
    (hr : ∀ s a, 0 ≤ M.R s a ∧ M.R s a ≤ 1) (γ : ℝ) (hγ : 0 < γ ∧ γ < 1)
    (η : ℕ → ℝ) (Q0 : X → A → ℝ) (hQ0 : ∀ s a, 0 ≤ Q0 s a ∧ Q0 s a ≤ 1 / (1 - γ))
    (σ : ℕ → X → A → X) (T : ℕ) (hη : ∀ t, t ≤ T → 0 ≤ η t ∧ η t ≤ 1)
    (Q : ℕ → X → A → ℝ) (hQ : Q = syncQ M γ η Q0 σ)
    (V : ℕ → X → ℝ) (hV : ∀ i, V i = vmax (Q i))
    (Δ : ℕ → X → A → ℝ) (hΔ : ∀ i s a, Δ i s a = Q i s a - qStar M γ s a)
    (π : ℕ → X → A) (hπ : ∀ i, i < T → IsGreedy (Q i) (π i))
    (πs : X → A) (hπs : ∀ s a, qPi M γ (detPolicy πs) s a = qStar M γ s a) :
    ∀ t, 1 ≤ t → t ≤ T → ∀ s a,
      (Δ t s a ≤ (1 - η t) * Δ (t - 1) s a + η t * γ *
          (PiOp M (π (t - 1)) (Δ (t - 1)) s a +
            (V (t - 1) (σ t s a) - ∑ s', M.P s a s' * V (t - 1) s'))) ∧
      (Δ t s a ≥ (1 - η t) * Δ (t - 1) s a + η t * γ *
          (PiOp M πs (Δ (t - 1)) s a +
            (V (t - 1) (σ t s a) - ∑ s', M.P s a s' * V (t - 1) s'))) ∧
      (Δ t s a ≤ weight η t 0 * Δ 0 s a + ∑ i ∈ Finset.Icc 1 t, weight η t i * γ *
          (PiOp M (π (i - 1)) (Δ (i - 1)) s a +
            (V (i - 1) (σ i s a) - ∑ s', M.P s a s' * V (i - 1) s'))) ∧
      (Δ t s a ≥ weight η t 0 * Δ 0 s a + ∑ i ∈ Finset.Icc 1 t, weight η t i * γ *
          (PiOp M πs (Δ (i - 1)) s a +
            (V (i - 1) (σ i s a) - ∑ s', M.P s a s' * V (i - 1) s'))) := by sorry

end TightQLearning
