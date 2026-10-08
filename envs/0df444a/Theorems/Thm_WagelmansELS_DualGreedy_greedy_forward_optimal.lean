-- Prove2me | Theorems.Thm_WagelmansELS_DualGreedy_greedy_forward_optimal
-- name    : WagelmansELS.DualGreedy.greedy_forward_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:58:04.514147+00:00
-- url     : https://prove2.me/theorems/a9b34dde-82f2-45f1-ab8c-9dd5585403dd
-- title:
--   Section 4 — greedy forward D′ solution is optimal
-- statement:
--   For an economic lot-sizing instance with nonnegative demands and setup costs and unrestricted marginal costs, let $v$ be any vector satisfying the greedy forward rule. Then $v$ satisfies every constraint of Program D′, each prefix objective equals the forward lot-sizing cost,
--
--   $$\sum_{t=1}^{j}d_tv_t=F(j)\qquad(1\le j\le n),$$
--
--   and no feasible vector $u$ has a larger full-horizon objective:
--
--   $$\sum_{t=1}^{n}d_tu_t\le\sum_{t=1}^{n}d_tv_t=F(n).$$
--
--   Thus every greedy forward choice, including arbitrary values at zero-demand periods, is optimal for D′. The identification of $F(n)$ with the primal optimum follows the paper's zero-inventory property and is outside this formal statement.
-- source:
--   Wagelmans, Van Hoesel and Kolen, Economic Lot Sizing, Oper. Res. 40 Supp. 1 (1992), p. S153, Section 4, paragraphs from “To prove optimality” through “yields the desired result”

import Mathlib
import Definitions.Def_WagelmansELS_DualGreedy_Greedy

namespace WagelmansELS.DualGreedy

theorem greedy_forward_optimal (P : Instance) (v : ℕ → ℝ)
    (hd : ∀ t, 1 ≤ t → t ≤ P.n → 0 ≤ P.d t)
    (hf : ∀ i, 1 ≤ i → i ≤ P.n → 0 ≤ P.f i)
    (hv : IsGreedyForward P v) :
    IsFeasible P v ∧
      (∀ j, 1 ≤ j → j ≤ P.n → objective P v j = F P j) ∧
      (∀ u, IsFeasible P u → objective P u P.n ≤ objective P v P.n) := by sorry

end WagelmansELS.DualGreedy
