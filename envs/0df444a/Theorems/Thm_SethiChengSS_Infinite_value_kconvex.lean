-- Prove2me | Theorems.Thm_SethiChengSS_Infinite_value_kconvex
-- name    : SethiChengSS.Infinite.value_kconvex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:00.920982+00:00
-- url     : https://prove2.me/theorems/e51397d6-1082-4509-84d7-46b3b1130810
-- title:
--   Proof of Theorem 6.2, p. 937 — the value function v_n(i, ·) is K^i_n-convex
-- statement:
--   Under the standing assumptions (2.1)–(2.2), assumptions (4.1) and (4.2) for every period, and $0 < \alpha < 1$, the value function $v_n(i,x) = \inf_U J_n(i,x;U)$ of the infinite-horizon problem is $K^i_n$-convex in $x$ for every $n$ and $i$:
--   $$K^i_n + v_n(i, z+y) \ge v_n(i,y) + z\,\frac{v_n(i,y) - v_n(i,y-b)}{b} \qquad (z \ge 0,\ b > 0).$$
--
--   $K$-convexity of the value function is what turns a minimizer of the optimality equation (6.2) into an $(s,S)$ rule.
--
--   **Formalization Note.** The value function is finite under these hypotheses and is taken as a real function. (4.1) is added for every period, as for the truncated values; $\alpha < 1$ as throughout.
-- source:
--   Sethi and Cheng, Optimality of (s, S) policies in inventory models with Markovian demand, Oper. Res. 45(6) (1997), DOI 10.1287/opre.45.6.931, p. 937, proof of Theorem 6.2, third sentence

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_SethiChengSS_Infinite_Model

namespace SethiChengSS.Infinite

theorem value_kconvex {L : ℕ} (D : Model L) (α : ℝ) (hD : Standing D) (h41 : Cond41 D)
    (h42 : Cond42 D) (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ n i, BertsekasKConvex (D.K n i) (fun x => (value D α n i x).toReal) := by sorry

end SethiChengSS.Infinite
