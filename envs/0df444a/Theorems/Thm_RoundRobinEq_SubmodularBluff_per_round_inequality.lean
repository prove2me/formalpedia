-- Prove2me | Theorems.Thm_RoundRobinEq_SubmodularBluff_per_round_inequality
-- name    : RoundRobinEq.SubmodularBluff.per_round_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:19:16.601231+00:00
-- url     : https://prove2.me/theorems/d0755e33-9a66-41c8-ae6f-c498ef3c6ad2
-- title:
--   §3.2, pp. 12–13, proof of Theorem 3.7 — per-round inequality v_i(X^j_−) − v_i(X^{j−1}_−) ≥ v_i(X^{j−1}_− ∪ Y^j_+) − v_i(X^j_− ∪ Y^{j+1}_+)
-- statement:
--   In the setting of Lemma 3.5 (submodular valuations, $m=kn$, a greedy bluff order $h$, an agent $i$ deviating to an arbitrary ranking, $X=\{x_1,\dots,x_k\}$ her bluff bundle in allocation order and $Y=\{y_1,\dots,y_k\}$ her deviation bundle in Algorithm 3 order), for every $j\in[k]$,
--   $$v_i(X^j_-)-v_i(X^{j-1}_-)\ \ge\ v_i(X^{j-1}_-\cup Y^j_+)-v_i(X^j_-\cup Y^{j+1}_+),$$
--   with $X^j_-=\{x_1,\dots,x_j\}$, $Y^j_+=\{y_j,\dots,y_k\}$, $X^0_-=\emptyset$ and $Y^{k+1}_+=\emptyset$.
--
--   Summed over $j$, the left side telescopes to $v_i(X)$ and the right side to $v_i(Y)-v_i(X)$.
--
--   **Formalization Note.** For `j : Fin k` (0-based, the paper's $j+1$), $X^{j}_-$ in the paper's indexing is `prefixSet x (j+1)`, $X^{j-1}_-$ is `prefixSet x j`, $Y^{j}_+$ is `suffixSet y j` and $Y^{j+1}_+$ is `suffixSet y (j+1)`. The hypotheses are those of Lemma 3.5. The paper does not assume $y_j\notin X^{j-1}_-$, and neither does the statement.
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, pp. 12–13, proof of Theorem 3.7, the chain of inequalities for j ∈ [k]

import Mathlib
import Definitions.Def_RoundRobinEq_SubmodularBluff_Setting
import Definitions.Def_RoundRobinEq_SubmodularBluff_Bluff
import Definitions.Def_RoundRobinEq_SubmodularBluff_Alg3

namespace RoundRobinEq.SubmodularBluff

theorem per_round_inequality {n : ℕ} [NeZero n] {M : Type*} [Fintype M] [DecidableEq M] (k : ℕ)
    (hm : Fintype.card M = k * n) (v : Fin n → Finset M → ℝ)
    (hv : ∀ i, RoundRobinEq.CancelableBluff.IsValuation (v i) ∧ IsSubmodular (v i))
    (h : List M) (hh : IsGreedyOrder v h) (i : Fin n) (τ : List M) (hτ : RoundRobinEq.CancelableBluff.IsRanking τ)
    (x : Fin k → M) (hx : ∀ j : Fin k, h[j.val * n + i.val]? = some (x j))
    (y : Fin k → M) (hy_inj : Function.Injective y)
    (hy : Finset.univ.image y = RoundRobinEq.CancelableBluff.roundRobin (Function.update (bluff h) i τ) i)
    (hy3 : IsAlg3Order (v i) x y) :
    ∀ j : Fin k,
      v i (prefixSet x j.val ∪ suffixSet y j.val) - v i (prefixSet x (j.val + 1) ∪ suffixSet y (j.val + 1)) ≤
        v i (prefixSet x (j.val + 1)) - v i (prefixSet x j.val) := by sorry

end RoundRobinEq.SubmodularBluff
