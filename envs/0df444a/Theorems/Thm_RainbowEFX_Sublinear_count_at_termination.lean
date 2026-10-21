-- Prove2me | Theorems.Thm_RainbowEFX_Sublinear_count_at_termination
-- name    : RainbowEFX.Sublinear.count_at_termination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:21.902731+00:00
-- url     : https://prove2.me/theorems/d04db5c9-ef1f-45a6-809d-662829ec679d
-- title:
--   p. 14, "Putting it together" — at termination |H_X| + |L_X| ≤ 2 · max(2n/(ε · d), 2d⁴)
-- statement:
--   Throughout, $[n]$ is the set of agents and $M$ the set of $m$ indivisible goods; agent $i$ has an additive valuation $v_i$ with $v_i(S)=\sum_{g\in S}v_i(\{g\})\ge 0$. A (partial) allocation $X=\langle X_1,\dots,X_n\rangle$ consists of pairwise disjoint bundles, and $P = M\setminus\bigcup_i X_i$ is the set (pool) of unallocated goods.
--
--   Let $n\ge1$, $0<\varepsilon\le1/2$, $d\ge1$, and let $X$ be a $(1-\varepsilon)$-EFX allocation satisfying assumption (\*) with $|L_X|\le d^4+d$ (the state in which the algorithm stops). Then the number of unallocated goods satisfies
--   $$
--   |P|=|H_X|+|L_X|\le 2\cdot\max\Big(\frac{2n}{\varepsilon\cdot d},\,2d^4\Big).
--   $$
--
--   With $d$ chosen as in the next milestone, this gives Theorem 1's bound.
--
--   **Formalization Note** This is the bracketed (algorithmic) variant on p. 14, with $|L_X|\le d^4+d$ instead of $|L_X|\le R(d)$. $n\ge 1$ is needed for Observation 12, which it uses.
-- source:
--   Chaudhury, Garg, Mehlhorn, Mehta, Misra, Improving EFX Guarantees through Rainbow Cycle Number, arXiv:2103.01628v1, p. 14, "Putting it together"

import Mathlib
import Definitions.Def_RainbowEFX_Sublinear_Setting

namespace RainbowEFX.Sublinear

open LittleCharity.EFX

theorem count_at_termination {n m : ℕ} (hn : 0 < n) (v : Fin n → Finset (Fin m) → ℝ)
    (hv : LittleCharity.MMS.IsAdditive v) (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2)
    (X : Fin n → Finset (Fin m)) (hX : IsPartialAllocation X) (hEFX : IsAlphaEFX (1 - ε) v X)
    (d : ℕ) (hd : 1 ≤ d) (hstar : Star ε v X) (hL : (LX ε v X d).card ≤ d ^ 4 + d) :
    ((pool X).card : ℝ) ≤ 2 * max (2 * n / (ε * d)) (2 * (d : ℝ) ^ 4) := by sorry

end RainbowEFX.Sublinear
