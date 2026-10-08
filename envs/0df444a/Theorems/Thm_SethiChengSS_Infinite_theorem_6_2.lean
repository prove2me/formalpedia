-- Prove2me | Theorems.Thm_SethiChengSS_Infinite_theorem_6_2
-- name    : SethiChengSS.Infinite.theorem_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:05.96037+00:00
-- url     : https://prove2.me/theorems/6d59ec3e-2076-41f0-bc08-5e797ebbd07a
-- title:
--   Theorem 6.2, p. 937 — in the discounted infinite-horizon problem, a state-dependent (s, S) feedback policy attains (6.2) and is optimal
-- statement:
--   Consider the Markov-modulated inventory model with fixed ordering costs over an infinite horizon, under the standing assumptions (2.1)–(2.2), assumptions (4.1) and (4.2) for every period, and a discount factor $0 < \alpha < 1$. Let $v_n$ be the value function of the infinite-horizon problem. Then there are extended real numbers $s^i_n \le S^i_n$, $n = 0, 1, 2, \dots$, $i \in I$, with $S^i_n < +\infty$ and $S^i_n$ real whenever $s^i_n > -\infty$, such that the $(s,S)$ rule
--   $$\hat u_n(i,x) = (S^i_n - x)\,\delta(s^i_n - x)$$
--   is an optimal feedback policy, in both senses:
--
--   1. for every $n$, $i$, $x$ it attains the infimum in the dynamic programming equation
--   $$\inf_{u\ge0}\big\{c_n(i,u) + \alpha F_{n+1}(v_{n+1})(i,x+u)\big\};$$
--   2. for every $n$, $i$, $x$ its feedback policy (3.3), started in period $n$ at surplus $x$, is admissible and its cost equals the value: $J_n(i,x;\hat U) = v_n(i,x)$, the infimum over all admissible history-dependent policies.
--
--   This is the infinite-horizon counterpart of the finite-horizon $(s,S)$ theorem (Theorem 4.1): with Markov-modulated demand and nonstationary data, an order-up-to rule whose two levels depend on the period and on the current demand state is optimal.
--
--   **Formalization Note.** The paper prints $0 < \alpha \le 1$; $\alpha < 1$ is assumed (at $\alpha = 1$ the costs are infinite in general and the Appendix divides by $1-\alpha$). Theorem 6.2 as printed assumes (2.1), (2.2) and (4.2) only; its proof uses the $K$-convexity induction of Section 4, which needs (4.1), so (4.1) is added for every period. The levels are extended reals as allowed by Remark 4.4: $s^i_n = -\infty$ means never order, $S^i_n = +\infty$ is excluded. The value function is finite under these hypotheses and is used as a real function in item 1.
-- source:
--   Sethi and Cheng, Optimality of (s, S) policies in inventory models with Markovian demand, Oper. Res. 45(6) (1997), DOI 10.1287/opre.45.6.931, p. 937, Theorem 6.2

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_SethiChengSS_Infinite_Model

namespace SethiChengSS.Infinite

theorem theorem_6_2 {L : ℕ} (D : Model L) (α : ℝ) (hD : Standing D) (h41 : Cond41 D)
    (h42 : Cond42 D) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ s S : ℕ → Fin L → EReal,
      (∀ n i, s n i ≤ S n i ∧ S n i ≠ ⊤ ∧ (s n i ≠ ⊥ → S n i ≠ ⊥)) ∧
      AttainsInf D α (fun n i x => (value D α n i x).toReal)
        (fun n i x => orderSS (s n i) (S n i) x) ∧
      ∀ n i x,
        Admissible (feedback (fun n i x => orderSS (s n i) (S n i) x) n x) ∧
        Jinf D α n i x (feedback (fun n i x => orderSS (s n i) (S n i) x) n x) =
          value D α n i x := by sorry

end SethiChengSS.Infinite
