-- Prove2me | Theorems.Thm_SethiChengSS_Infinite_truncated_dp
-- name    : SethiChengSS.Infinite.truncated_dp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:37.589792+00:00
-- url     : https://prove2.me/theorems/a0935274-4089-4d37-a521-5ef7b3a152b9
-- title:
--   Eq. (6.5), pp. 936–937 — the truncated value v_{n,k} solves the DP (6.5), v_{n,0} = 0, v_{n,k} ∈ C_1, and under (4.2) the infimum in (6.4) is attained
-- statement:
--   Under the standing assumptions (2.1)–(2.2) and $0 < \alpha < 1$, let $v_{n,k}(i,x) = \inf_{U} J_{n,k}(i,x;U)$ be the value of the $k$-period truncation (6.4) of the infinite-horizon problem, the infimum running over all admissible history-dependent policies. Let $V_{n,k}$ be defined by the dynamic programming recursion
--   $$V_{n,0} = 0, \qquad V_{n,k+1}(i,x) = f_n(i,x) + \inf_{u\ge0}\big\{c_n(i,u) + \alpha F_{n+1}(V_{n+1,k})(i,x+u)\big\}. \tag{6.5}$$
--   Then
--
--   1. $v_{n,k} = V_{n,k}$ for all $n$, $k$, $i$, $x$;
--   2. $v_{n,0} = 0$;
--   3. $v_{n,k} \in C_1$;
--   4. if in addition (4.2) holds for every period, the infimum in (6.4) is attained by an admissible policy.
--
--   This is the finite-horizon theory (Theorems 3.1–3.2 of the paper) applied to each truncation; it is the starting point of the successive approximation of the infinite-horizon problem.
--
--   **Formalization Note.** The paper prints "$v_{n+k,0}(i,x) = 0$" in (6.5); the next sentence ("$v_{n,0}(i,x) = 0$") shows the boundary condition is $v_{n,0} = 0$, which is what the recursion encodes. Attainment is stated under (4.2): without a coercivity condition the infimum in the DP need not be attained (one demand state, $c = 0$, $f(x) = \max(-x,0)$, exponential demand), and the paper's attainment claim rests on Theorem 3.1, whose proof is not in the paper.
-- source:
--   Sethi and Cheng, Optimality of (s, S) policies in inventory models with Markovian demand, Oper. Res. 45(6) (1997), DOI 10.1287/opre.45.6.931, pp. 936–937, (6.4)–(6.5) and the sentence after (6.5)

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_SethiChengSS_Infinite_Model

namespace SethiChengSS.Infinite

theorem truncated_dp {L : ℕ} (D : Model L) (α : ℝ) (hD : Standing D) (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ n k i x, vTrunc D α n k i x = ENNReal.ofReal (dpTrunc D α n k i x)) ∧
    (∀ n i x, vTrunc D α n 0 i x = 0) ∧
    (∀ n k, InC1 (fun i x => (vTrunc D α n k i x).toReal)) ∧
    (Cond42 D → ∀ n k i x, ∃ U : Policy L, Admissible U ∧
      Jtrunc D α n k i x U = vTrunc D α n k i x) := by sorry

end SethiChengSS.Infinite
