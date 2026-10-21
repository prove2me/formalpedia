-- Prove2me | Theorems.Thm_RevConvexDisj_MultiTerm_theorem_5_TC_subset
-- name    : RevConvexDisj.MultiTerm.theorem_5_TC_subset
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:55.979776+00:00
-- url     : https://prove2.me/theorems/8ffa45f5-b75d-481d-846c-4fd51ad372a2
-- title:
--   Proof of Theorem 5, p. 18 — T^C ⊆ S^C_k for all k ∈ N2 ∪ {0}
-- statement:
--   In the setting of Theorem 5 ($C$ open and convex, $\bar x\notin\operatorname{cl}(C)$, Assumption 2: $\operatorname{recc}(C)\subseteq\operatorname{recc}(P^B)$), the inner approximation $T^C = \{\bar x\}+\operatorname{conv}(\bigcup_{j\in N_0^{\mathrm c}}(\alpha_j,\beta_j)\bar r^j)+\operatorname{recc}(C)$ is contained in every disjunctive term:
--   $$T^C\subseteq S^C_0\qquad\text{and}\qquad T^C\subseteq S^C_k\ \text{ for every } k\in N_2.$$
--
--   This is the easy inclusion $T^C\subseteq\bigcap_{k\in N_2^0}S^C_k$ of the proof of Theorem 5, with $N_2^0 = N_2\cup\{0\}$.
--
--   **Formalization Note.** The index set $N_2^0=N_2\cup\{0\}$ is not a type; the term "$k=0$" is $S^C_0$ and the others are $S^C_k$ for $k\in N_2$.
-- source:
--   Towle & Luedtke, Intersection disjunctions for reverse convex sets, arXiv:1901.02112v5, p. 18, proof of Theorem 5, "By construction, T^C ⊆ S^C_k for all k ∈ N^0_2"

import Mathlib
import Definitions.Def_RevConvexDisj_MultiTerm_Model

namespace RevConvexDisj.MultiTerm

theorem theorem_5_TC_subset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : BasisData ι) (C : Set (ι → ℝ))
    (hCopen : IsOpen C) (hCconv : Convex ℝ C) (hxbar : D.xbar ∉ closure C)
    (hA2 : recc C ⊆ recc D.PB) :
    TC D C ⊆ SC0 D C ∧ ∀ k ∈ N2 D C, TC D C ⊆ SCk D C k := by sorry

end RevConvexDisj.MultiTerm
