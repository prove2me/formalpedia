-- Prove2me | Theorems.Thm_ThomsonKS_Char_theorem_3
-- name    : ThomsonKS.Char.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:47:58.346708+00:00
-- url     : https://prove2.me/theorems/c04ff62a-faf8-4860-b7b2-560e13c7e475
-- title:
--   Theorem 3, p. 323 — a solution satisfying WPO, An, S. Inv, Cont and Mon is the Kalai–Smorodinsky solution
-- statement:
--   Let $F$ be a solution: for every finite group $P$ of agents and every $S \in \Sigma^P$ it selects a point $F^P(S) \in S$. If $F$ satisfies weak Pareto-optimality (WPO), anonymity (An), scale invariance (S. Inv), continuity in the Hausdorff metric (Cont) and population monotonicity (Mon), then
--
--   $$F^P(S) = K^P(S) \qquad \text{for every finite group } P \text{ and every } S \in \Sigma^P,$$
--
--   where $K$ is the Kalai–Smorodinsky solution.
--
--   This is the uniqueness half of the characterization; Theorem 1 is the existence half.
--
--   **Formalization Note** "$F$ is the Kalai–Smorodinsky solution" is stated as agreement on every $\Sigma^P$, since a solution is only defined on those problems.
-- source:
--   Thomson, The fair division of a fixed supply among a growing population, Math. Oper. Res. 8 (1983), p. 323, Theorem 3

import Mathlib
import Definitions.Def_ThomsonKS_Char_Setting

namespace ThomsonKS.Char

theorem theorem_3 (F : Solution) (hF : IsSolution F) (hW : WPO F) (hA : An F)
    (hI : SInv F) (hC : Cont F) (hM : Mon F) :
    ∀ P : Finset ℕ, ∀ S ∈ DivProb P, F P S = KS P S := by sorry

end ThomsonKS.Char
