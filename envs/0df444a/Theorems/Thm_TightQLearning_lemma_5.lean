-- Prove2me | Theorems.Thm_TightQLearning_lemma_5
-- name    : TightQLearning.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:33:31.996877+00:00
-- url     : https://prove2.me/theorems/2398c2bb-c5bb-4f18-a882-8249c7f9e002
-- title:
--   Lemma 5 — the total-variance bound (85)
-- statement:
--   Let $\gamma\in(0,1)$, let the rewards lie in $[0,1]$, let $t\ge2$, let $Q_i$ satisfy $0\le Q_i\le\frac1{1-\gamma}$ on the window $t/2\le i<t$, and let $\pi_i$ be greedy selections of $Q_i$. Let $H$ be a natural number and let $i_1,\dots,i_H$ lie in the window. Then, entrywise,
--   $$\sum_{h=0}^{H-1}\gamma^h\prod_{k=1}^hP^{\pi_{i_k}}\max_{t/2\le i<t}\mathsf{Var}_P(V_i)\le\frac4{\gamma^2(1-\gamma)^2}\Big(1+2\max_{t/2\le i<t}\|\Delta_i\|_\infty\Big)\mathbf 1,$$
--   where the maximum inside is taken entrywise and the rightmost factor of the product acts first.
--
--   This bound shaves one factor $\frac1{1-\gamma}$ from the crude estimate, even though the policies change along the product. It is the key new ingredient of the $\frac1{(1-\gamma)^4}$ rate.
--
--   Differences from the source:
--   - encoding: the state and action spaces are {1,…,|S|} and {1,…,|A|} → finite nonempty types X and A; reason: the instances are the same up to relabelling; |S||A| is Fintype.card X * Fintype.card A
--   - encoding: V^π and Q^π are expectations along a trajectory → the published PolicyValue series, with QFunction for the first step; reason: the series computes the expectation term by term; Q^π is r + γPV^π, the trajectory with a₀ fixed
--   - encoding: max over t/2 ≤ i < t, which is undefined for t = 1 → the hypothesis 2 ≤ t, and windowMax over a nonempty window; reason: it excludes only the case where the printed maximum is undefined
--   - generalization: π_t picks the smallest maximizing index (27) → any greedy selection; reason: (27) is one such selection
--   - generalization: H = log T/(1−γ) and (i₁,…,i_H) ∈ I_t, with t ≥ T/(c₂ log T) → every natural H, every list in the window, every t ≥ 2; reason: I_t lies in the window (p.24), so this covers every rounding of H; the page's telescoping proof uses none of these restrictions
--   - generalization: V_i are the iterates of Algorithm 1 → any sequence in the box on the window; reason: the page's proof uses only the box
-- source:
--   Li, Cai, Chen, Wei & Chi, Is Q-Learning Minimax Optimal? A Tight Sample Complexity Analysis, arXiv:2102.06548v4 (https://arxiv.org/abs/2102.06548v4), Lemma 5, (85), p.25

import Mathlib
import Definitions.Def_TightQLearning_qStar
import Definitions.Def_TightQLearning_IsGreedy
import Definitions.Def_TightQLearning_piProd
import Definitions.Def_TightQLearning_window
import Definitions.Def_TightQLearning_windowMax
import Definitions.Def_BreakingSample_Perturbed_Model

open QLearning.Convergence

namespace TightQLearning

/-- Lemma 5, (85) (Li, Cai, Chen, Wei & Chi, arXiv:2102.06548v4, p.25), the total-variance bound,
entrywise:
`∑_{h=0}^{H−1} γ^h ∏_{k=1}^h P^{π_{i_k}} max_{t/2≤i<t} Var_P(V_i)
  ≤ (4/(γ²(1−γ)²)) (1 + 2 max_{t/2≤i<t} ‖Δ_i‖_∞) 1`.

**Formalization Note.** The page fixes `H = log T/(1−γ)` (80) and `(i₁,…,i_H) ∈ I_t` (82), both
under the standing setting of Appendix B. The bound is deterministic and is stated for every
natural `H` and every index list in the window `[t/2, t)`, for every sequence in the box with any
greedy selections, which covers every rounding of `H` and the whole of `I_t`. The list
`[π_{i_1}, …, π_{i_h}]` is applied by `piProd`, with `P^{π_{i_h}}` acting first. -/
theorem lemma_5 {X A : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype A] [DecidableEq A] [Nonempty A] (M : FiniteMDP X A)
    (hr : ∀ s a, 0 ≤ M.R s a ∧ M.R s a ≤ 1) (γ : ℝ) (hγ : 0 < γ ∧ γ < 1)
    (t : ℕ) (ht : 2 ≤ t) (Q : ℕ → X → A → ℝ)
    (hQ : ∀ i ∈ window t, ∀ s a, 0 ≤ Q i s a ∧ Q i s a ≤ 1 / (1 - γ))
    (π : ℕ → X → A) (hπ : ∀ i ∈ window t, IsGreedy (Q i) (π i))
    (H : ℕ) (idx : ℕ → ℕ) (hidx : ∀ k, 1 ≤ k → k ≤ H → idx k ∈ window t) (s : X) (a : A) :
    ∑ h ∈ Finset.range H, γ ^ h *
        piProd M ((List.range h).map (fun k => π (idx (k + 1))))
          (fun s' a' => windowMax t ht
            (fun i => BreakingSample.Perturbed.varP M.P (vmax (Q i)) s' a')) s a ≤
      4 / (γ ^ 2 * (1 - γ) ^ 2) * (1 + 2 * windowMax t ht (fun i => ‖Q i - qStar M γ‖)) := by sorry

end TightQLearning
