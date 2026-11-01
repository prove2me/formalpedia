-- Prove2me | Theorems.Thm_TightQLearning_eq_95
-- name    : TightQLearning.eq_95
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:33:34.101057+00:00
-- url     : https://prove2.me/theorems/734080f0-08fd-440c-9ceb-aad1eeced6fd
-- title:
--   (95) — $\max_{t/2\le i<t}\mathsf{Var}_P(V_i)-\mathsf{Var}_P(V^\star)\le\frac4{1-\gamma}\max_{t/2\le i<t}\|\Delta_i\|_\infty\mathbf 1$
-- statement:
--   Let $\gamma\in(0,1)$, let the rewards lie in $[0,1]$, let $t\ge2$, and let $Q_i$ be functions with $0\le Q_i\le\frac1{1-\gamma}$ for $t/2\le i<t$. Write $V_i=\max_aQ_i(\cdot,a)$ and $\Delta_i=Q_i-Q^\star$, and let $\mathsf{Var}_P(V)(s,a)$ be the variance of $V(s')$ under $s'\sim P(\cdot\mid s,a)$. Then for every $(s,a)$,
--   $$\max_{t/2\le i<t}\mathsf{Var}_P(V_i)(s,a)-\mathsf{Var}_P(V^\star)(s,a)\le\frac4{1-\gamma}\max_{t/2\le i<t}\|\Delta_i\|_\infty.$$
--
--   The bound moves the variance of the running iterates onto the variance of $V^\star$, up to the error being controlled. It is the first step in the proof of Lemma 5.
--
--   Differences from the source:
--   - encoding: the state and action spaces are {1,…,|S|} and {1,…,|A|} → finite nonempty types X and A; reason: the instances are the same up to relabelling; |S||A| is Fintype.card X * Fintype.card A
--   - encoding: V^π and Q^π are expectations along a trajectory → the published PolicyValue series, with QFunction for the first step; reason: the series computes the expectation term by term; Q^π is r + γPV^π, the trajectory with a₀ fixed
--   - encoding: max over t/2 ≤ i < t, which is undefined for t = 1 → the hypothesis 2 ≤ t, and windowMax over a nonempty window; reason: it excludes only the case where the printed maximum is undefined
--   - generalization: V_i are the iterates of Algorithm 1 → any sequence in the box of Lemma 4 on the window; reason: the page's proof uses only that box, which Lemma 4 gives for the iterates
-- source:
--   Li, Cai, Chen, Wei & Chi, Is Q-Learning Minimax Optimal? A Tight Sample Complexity Analysis, arXiv:2102.06548v4 (https://arxiv.org/abs/2102.06548v4), (95), p.28

import Mathlib
import Definitions.Def_TightQLearning_vStar
import Definitions.Def_TightQLearning_qStar
import Definitions.Def_TightQLearning_window
import Definitions.Def_TightQLearning_windowMax
import Definitions.Def_BreakingSample_Perturbed_Model

open QLearning.Convergence

namespace TightQLearning

/-- The variance comparison (95) (Li, Cai, Chen, Wei & Chi, arXiv:2102.06548v4, p.28), entrywise:
`max_{t/2≤i<t} Var_P(V_i) − Var_P(V⋆) ≤ (4/(1−γ)) max_{t/2≤i<t} ‖Δ_i‖_∞ 1`.

**Formalization Note.** The bound is deterministic: it holds for every sequence in the box of
Lemma 4 on the window, which is the only property of the iterates the page's proof uses. `‖·‖` on
`X → A → ℝ` is the sup norm. -/
theorem eq_95 {X A : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype A] [DecidableEq A] [Nonempty A] (M : FiniteMDP X A)
    (hr : ∀ s a, 0 ≤ M.R s a ∧ M.R s a ≤ 1) (γ : ℝ) (hγ : 0 < γ ∧ γ < 1)
    (t : ℕ) (ht : 2 ≤ t) (Q : ℕ → X → A → ℝ)
    (hQ : ∀ i ∈ window t, ∀ s a, 0 ≤ Q i s a ∧ Q i s a ≤ 1 / (1 - γ)) (s : X) (a : A) :
    windowMax t ht (fun i => BreakingSample.Perturbed.varP M.P (vmax (Q i)) s a)
        - BreakingSample.Perturbed.varP M.P (vStar M γ) s a ≤
      4 / (1 - γ) * windowMax t ht (fun i => ‖Q i - qStar M γ‖) := by sorry

end TightQLearning
