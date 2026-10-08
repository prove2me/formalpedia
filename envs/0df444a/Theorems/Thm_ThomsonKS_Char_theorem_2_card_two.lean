-- Prove2me | Theorems.Thm_ThomsonKS_Char_theorem_2_card_two
-- name    : ThomsonKS.Char.theorem_2_card_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:47:40.465064+00:00
-- url     : https://prove2.me/theorems/5c95fcf6-d0df-4a00-a710-374ce2f0eea9
-- title:
--   Theorem 2 for |P| = 2, pp. 321–322 — under WPO, An, S. Inv and Mon, F^P(S) ≧ K^P(S) for two-agent groups
-- statement:
--   Let $F$ be a solution: for every finite group $P$ of agents and every $S \in \Sigma^P$ it selects a point $F^P(S) \in S$. Suppose $F$ satisfies weak Pareto-optimality (WPO), anonymity (An), scale invariance (S. Inv) and population monotonicity (Mon). Then for every two-agent group $P$ ($|P| = 2$) and every $S \in \Sigma^P$,
--
--   $$F^P(S) \geqq K^P(S),$$
--
--   i.e. $F^P_i(S) \ge K^P_i(S)$ for both agents $i \in P$, where $K$ is the Kalai–Smorodinsky solution.
--
--   This is the case of Theorem 2 that the paper proves in the body of §3, by adding a single third agent; the general case is Theorem 2 (appendix).
--
--   **Formalization Note** Continuity is not assumed. The statement is the "only if" content of Theorem 2 restricted to $|P| = 2$; the printed "if" direction is not part of it (see the Theorem 2 item).
-- source:
--   Thomson, The fair division of a fixed supply among a growing population, Math. Oper. Res. 8 (1983), pp. 321–322, Theorem 2, proof for |P| = 2 in §3

import Mathlib
import Definitions.Def_ThomsonKS_Char_Setting

namespace ThomsonKS.Char

theorem theorem_2_card_two (F : Solution) (hF : IsSolution F) (hW : WPO F) (hA : An F)
    (hI : SInv F) (hM : Mon F) (P : Finset ℕ) (hP : P.card = 2) (S : Set (P → ℝ))
    (hS : S ∈ DivProb P) : KS P S ≤ F P S := by sorry

end ThomsonKS.Char
