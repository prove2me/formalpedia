-- Prove2me | Theorems.Thm_ThomsonKS_Char_theorem_1
-- name    : ThomsonKS.Char.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:47:39.602579+00:00
-- url     : https://prove2.me/theorems/77a519db-c9f7-450e-a372-2d7d0d84cfc5
-- title:
--   Theorem 1, p. 321 — the Kalai–Smorodinsky solution satisfies WPO, An, S. Inv, Cont and Mon
-- statement:
--   Let $K = \{K^P\}$ be the Kalai–Smorodinsky solution: for every finite group $P$ of agents and every division problem $S \in \Sigma^P$, $K^P(S)$ is the largest point of $S$ on the segment from the origin to the ideal point $a(S)$, $a_i(S) = \max_{x \in S} x_i$. Then
--
--   $$K^P(S) \in S \text{ for all } S \in \Sigma^P, \quad\text{and } K \text{ satisfies WPO, An, S. Inv, Cont and Mon.}$$
--
--   That is: $K^P(S)$ is weakly Pareto-optimal in $S$; it commutes with relabellings of the agents; it commutes with positive coordinatewise rescalings of utilities; it depends continuously on $S$ in the Hausdorff metric; and when a group $P$ is enlarged to $Q \supseteq P$ with $S = T \cap \mathbb R^P$, no member of $P$ receives more in $T$ than in $S$, $K^Q_i(T) \le K^P_i(S)$.
--
--   This is the sufficiency half of the paper's characterization of the Kalai–Smorodinsky solution.
--
--   **Formalization Note** The fact that $K^P(S)$ is a point of $S$ for every $S \in \Sigma^P$ is implicit on the page (the solution selects "the maximal element of $S$ on the segment"); it is stated here as the first conjunct `IsSolution KS`.
-- source:
--   Thomson, The fair division of a fixed supply among a growing population, Math. Oper. Res. 8 (1983), p. 321, Theorem 1

import Mathlib
import Definitions.Def_ThomsonKS_Char_Setting

namespace ThomsonKS.Char

theorem theorem_1 : IsSolution KS ∧ WPO KS ∧ An KS ∧ SInv KS ∧ Cont KS ∧ Mon KS := by sorry

end ThomsonKS.Char
