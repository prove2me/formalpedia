-- Prove2me | Theorems.Thm_SuttonBartoRL_NStep_treeBackupReturn_eq_sum_tdError
-- name    : SuttonBartoRL.NStep.treeBackupReturn_eq_sum_tdError
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T06:58:39.605722+00:00
-- url     : https://prove2.me/theorems/257f5c64-6068-4f1c-aca9-2d369d463ee8
-- title:
--   The tree-backup return as a sum of expectation-based TD errors (Exercise 7.11)
-- statement:
--   Consider an episode $S_0, A_0, R_1, S_1, A_1, \dots, R_T, S_T$ that terminates at time $T$, a target policy $\pi$, a discount $\gamma$, and action values $Q$ that do not change, with $Q(S_T, a) = 0$ for every action $a$. Let $\bar V(s) = \sum_a \pi(a \mid s) Q(s, a)$ be the expected approximate value (7.8), $\delta_k = R_{k+1} + \gamma \bar V(S_{k+1}) - Q(S_k, A_k)$ the expectation-based TD error, and $G_{t:t+n}$ the tree-backup return of (7.15)–(7.16) ($G_{T-1:t+n} = R_T$). Then for every $n \ge 1$ and $0 \le t < T$,
--   $$G_{t:t+n} = Q(S_t, A_t) + \sum_{k=t}^{\min(t+n-1,\,T-1)} \delta_k \prod_{i=t+1}^{k} \gamma\,\pi(A_i \mid S_i).$$
--
--   This shows that the tree-backup target corrects the current estimate by one-step expected TD errors, each discounted by the target-policy probabilities of the actions actually taken.
--
--   **Formalization Note** The book poses this as Exercise 7.11 and gives no solution. The hypothesis $Q(S_T, \cdot) = 0$ gives $\bar V(S_T) = 0$, which is the book's convention that the expected approximate value of a terminal state is $0$ (p. 148).
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Exercise 7.11, p. 153 (with (7.8), p. 148, and (7.15)–(7.16), p. 153)

import Mathlib
import Definitions.Def_SuttonBartoRL_NStep_EpisodeReturns

namespace SuttonBartoRL.NStep

/-- Sutton & Barto (2018), Exercise 7.11, p. 153: if the approximate action values `Q` are
unchanging and the terminal state has action value zero (`Q(S_T, a) = 0`, so `V̄(S_T) = 0`), the
tree-backup return (7.16) is a sum of expectation-based TD errors:
`G_{t:t+n} = Q(S_t, A_t) + Σ_{k=t}^{min(t+n−1, T−1)} δ_k Π_{i=t+1}^{k} γ π(A_i | S_i)`,
with `δ_k = R_{k+1} + γ V̄(S_{k+1}) − Q(S_k, A_k)` and `V̄` from (7.8), for `n ≥ 1` and `0 ≤ t < T`. -/
theorem treeBackupReturn_eq_sum_tdError {S A : Type} [Fintype A] [DecidableEq A]
    (π : Policy S A) (γ : ℝ) (R : ℕ → ℝ) (St : ℕ → S) (At : ℕ → A) (T : ℕ)
    (Q : S → A → ℝ) (hterm : ∀ a, Q (St T) a = 0) (t n : ℕ) (hn : 1 ≤ n) (ht : t < T) :
    treeBackupReturn π γ R St At T Q t (t + n) =
      Q (St t) (At t) +
        ∑ k ∈ Finset.Icc t (min (t + n - 1) (T - 1)),
          expectedTDError π γ R St At Q k *
            ∏ i ∈ Finset.Ioc t k, γ * π.prob (St i) (At i) := by sorry

end SuttonBartoRL.NStep
