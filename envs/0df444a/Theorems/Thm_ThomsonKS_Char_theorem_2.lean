-- Prove2me | Theorems.Thm_ThomsonKS_Char_theorem_2
-- name    : ThomsonKS.Char.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:48:01.528443+00:00
-- url     : https://prove2.me/theorems/ba09b8b6-241d-4363-9a0c-166e2566056f
-- title:
--   Theorem 2 ("only if"), pp. 321, 324–325 — a solution satisfying WPO, An, S. Inv and Mon dominates the Kalai–Smorodinsky solution
-- statement:
--   Let $F$ be a solution: for every finite group $P$ of agents and every $S \in \Sigma^P$ it selects a point $F^P(S) \in S$. If $F$ satisfies weak Pareto-optimality (WPO), anonymity (An), scale invariance (S. Inv) and population monotonicity (Mon), then
--
--   $$F^P(S) \geqq K^P(S) \qquad \text{for every finite group } P \text{ and every } S \in \Sigma^P,$$
--
--   where $K$ is the Kalai–Smorodinsky solution and $\geqq$ is the coordinatewise order.
--
--   This is the key step of the characterization: together with the fact that $K^P(S)$ is the only weakly Pareto-optimal point of $S$ on its ray, it pins $F$ down on problems where weak and strong Pareto-optimality agree (Corollary 1), and with continuity everywhere (Theorem 3).
--
--   **Formalization Note** The paper prints Theorem 2 as an "if and only if". Only the "only if" direction is stated here. The "if" direction, that every solution with $F \geqq K$ satisfies WPO, An, S. Inv and Mon, is false (a solution can dominate $K$ and violate S. Inv or An, e.g. by selecting $(2,1,1)$ on $\mathrm{cch}\{(2,1,1),(0,2,0),(0,0,2)\}$ and $K$ elsewhere), neither proof in the paper argues it, and no later result uses it.
-- source:
--   Thomson, The fair division of a fixed supply among a growing population, Math. Oper. Res. 8 (1983), p. 321 (statement), pp. 324–325 (Appendix, general proof), Theorem 2, 'only if' direction

import Mathlib
import Definitions.Def_ThomsonKS_Char_Setting

namespace ThomsonKS.Char

theorem theorem_2 (F : Solution) (hF : IsSolution F) (hW : WPO F) (hA : An F)
    (hI : SInv F) (hM : Mon F) : ∀ P : Finset ℕ, ∀ S ∈ DivProb P, KS P S ≤ F P S := by sorry

end ThomsonKS.Char
