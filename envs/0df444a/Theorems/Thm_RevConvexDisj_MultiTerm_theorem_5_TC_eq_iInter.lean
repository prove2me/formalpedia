-- Prove2me | Theorems.Thm_RevConvexDisj_MultiTerm_theorem_5_TC_eq_iInter
-- name    : RevConvexDisj.MultiTerm.theorem_5_TC_eq_iInter
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:56.626675+00:00
-- url     : https://prove2.me/theorems/8b88fbcf-2b02-4772-b750-3b4815988a03
-- title:
--   Proof of Theorem 5, p. 18 — T^C = ⋂_{k ∈ N2 ∪ {0}} S^C_k
-- statement:
--   In the setting of Theorem 5 ($C$ open and convex, $\bar x\notin\operatorname{cl}(C)$, Assumption 2: $\operatorname{recc}(C)\subseteq\operatorname{recc}(P^B)$), the inner approximation $T^C$ of $C$ is exactly the intersection of the disjunctive terms:
--   $$T^C = \bigcap_{k\in N_2^0}S^C_k = S^C_0\cap\bigcap_{k\in N_2}S^C_k,\qquad N_2^0 := N_2\cup\{0\}.$$
--
--   The paper reduces Theorem 5 to this identity; taking complements inside $P^B$ yields the multi-term disjunction (31).
--
--   **Formalization Note.** When $N_2=\emptyset$ the intersection over $N_2$ is the whole space and the identity reads $T^C = S^C_0$.
-- source:
--   Towle & Luedtke, Intersection disjunctions for reverse convex sets, arXiv:1901.02112v5, p. 18, proof of Theorem 5, "It suffices to show T^C = ⋂_{k∈N^0_2} S^C_k"

import Mathlib
import Definitions.Def_RevConvexDisj_MultiTerm_Model

namespace RevConvexDisj.MultiTerm

theorem theorem_5_TC_eq_iInter {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : BasisData ι) (C : Set (ι → ℝ))
    (hCopen : IsOpen C) (hCconv : Convex ℝ C) (hxbar : D.xbar ∉ closure C)
    (hA2 : recc C ⊆ recc D.PB) :
    TC D C = SC0 D C ∩ ⋂ k ∈ N2 D C, SCk D C k := by sorry

end RevConvexDisj.MultiTerm
