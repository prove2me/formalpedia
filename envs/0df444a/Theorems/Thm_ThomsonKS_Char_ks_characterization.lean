-- Prove2me | Theorems.Thm_ThomsonKS_Char_ks_characterization
-- name    : ThomsonKS.Char.ks_characterization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:48:59.507951+00:00
-- url     : https://prove2.me/theorems/706f011c-fed8-4b78-be59-73af0617b5e3
-- title:
--   Theorems 1 and 3, pp. 321, 323 — a solution satisfies WPO, An, S. Inv, Cont and Mon iff it is the Kalai–Smorodinsky solution
-- statement:
--   Consider a variable population of agents. For each nonempty finite group $P$, $\Sigma^P$ is the class of division problems: compact, convex, comprehensive subsets of $\mathbb R^P_+$ containing a strictly positive vector. A solution $F$ selects a point $F^P(S) \in S$ for every $P$ and every $S \in \Sigma^P$. Then
--
--   $$F \text{ satisfies WPO, An, S. Inv, Cont and Mon} \iff F^P(S) = K^P(S) \text{ for all finite } P \text{ and all } S \in \Sigma^P,$$
--
--   where $K$ is the Kalai–Smorodinsky solution ($K^P(S)$ is the largest point of $S$ on the segment from the origin to the ideal point $a(S)$, $a_i(S) = \max_{x\in S} x_i$). The axioms are: weak Pareto-optimality (no point of $S$ is strictly better for everyone), anonymity (invariance under relabelling the agents), scale invariance (covariance with positive rescalings of each agent's utility), continuity in the Hausdorff metric, and population monotonicity (when new agents arrive and the problem $S$ of the original group is the slice $T \cap \mathbb R^P$ of the enlarged problem $T$, no original agent gains).
--
--   The paper states: "Theorems 1 and 3 together constitute the announced characterization of the Kalai–Smorodinsky solution."
--
--   **Formalization Note** Agents are natural numbers and groups are nonempty finite sets of them (for the empty group no solution could satisfy WPO, see the Setting item). A solution is a total function together with the hypothesis that $F^P(S) \in S$ for $S \in \Sigma^P$; "is the Kalai–Smorodinsky solution" means agreement on every $\Sigma^P$, the only problems on which a solution is defined. Every axiom evaluates $F$ only on problems in $\Sigma^P$.
-- source:
--   Thomson, The fair division of a fixed supply among a growing population, Math. Oper. Res. 8 (1983), pp. 321, 323, Theorems 1 and 3 ('Theorems 1 and 3 together constitute the announced characterization', p. 323)

import Mathlib
import Definitions.Def_ThomsonKS_Char_Setting

namespace ThomsonKS.Char

theorem ks_characterization (F : Solution) (hF : IsSolution F) :
    (WPO F ∧ An F ∧ SInv F ∧ Cont F ∧ Mon F) ↔
      ∀ P : Finset ℕ, ∀ S ∈ DivProb P, F P S = KS P S := by sorry

end ThomsonKS.Char
