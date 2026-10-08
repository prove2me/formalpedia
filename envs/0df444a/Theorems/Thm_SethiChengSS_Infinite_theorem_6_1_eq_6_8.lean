-- Prove2me | Theorems.Thm_SethiChengSS_Infinite_theorem_6_1_eq_6_8
-- name    : SethiChengSS.Infinite.theorem_6_1_eq_6_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:37.566986+00:00
-- url     : https://prove2.me/theorems/fa758288-4ff4-45a3-95cb-3237fc42e9fb
-- title:
--   Theorem 6.1, (6.8), p. 937 — 0 = v_{n,0} ≤ v_{n,1} ≤ ⋯ ≤ v_{n,k} ≤ w_n
-- statement:
--   Under the standing assumptions (2.1)–(2.2) and $0 < \alpha < 1$, the values $v_{n,k}$ of the $k$-period truncations (6.4) increase in $k$ and are bounded by the order-nothing cost $w_n$ of (6.6):
--   $$0 = v_{n,0} \le v_{n,1} \le \cdots \le v_{n,k} \le w_n. \tag{6.8}$$
--
--   Monotonicity and the bound $w_n$ make the limit $v_n = \lim_k v_{n,k}$ exist, which is the first step of the successive approximation of the infinite-horizon problem.
--
--   **Formalization Note.** Values are in $[0,\infty]$. The paper allows $\alpha = 1$; $\alpha < 1$ is assumed throughout the mission (the Appendix divides by $1-\alpha$).
-- source:
--   Sethi and Cheng, Optimality of (s, S) policies in inventory models with Markovian demand, Oper. Res. 45(6) (1997), DOI 10.1287/opre.45.6.931, p. 937, Theorem 6.1, (6.8)

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_SethiChengSS_Infinite_Model

namespace SethiChengSS.Infinite

theorem theorem_6_1_eq_6_8 {L : ℕ} (D : Model L) (α : ℝ) (hD : Standing D) (hα0 : 0 < α)
    (hα1 : α < 1) :
    (∀ n i x, vTrunc D α n 0 i x = 0) ∧
    (∀ n k i x, vTrunc D α n k i x ≤ vTrunc D α n (k + 1) i x) ∧
    (∀ n k i x, vTrunc D α n k i x ≤ w D α n i x) := by sorry

end SethiChengSS.Infinite
