-- Prove2me | Theorems.Thm_SingleMachinePrec_ConvexBipartite_lemma_A_2
-- name    : SingleMachinePrec.ConvexBipartite.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:42:19.969225+00:00
-- url     : https://prove2.me/theorems/229be9d9-4ac1-452b-b030-d7750587d136
-- title:
--   Lemma A.2 — each $\bar E_m = E_m \cup P$ extends to a linear order
-- statement:
--   Let $\mathbf P$ be a convex bipartite order whose plus jobs are numbered so that a smaller index never has a larger left end: for plus jobs $j_i, j_j$, $i < j$ implies $l(i) \le l(j)$ (the standing assumption of the Appendix, p. 667). Let $\bar E_m = E_m \cup P$ for $m = 1, 2, 3$. Then each $\bar E_m$ is an extension of $P$ in the sense used by the paper: it contains $P$ and it contains no cycle, so that it is contained in a linear order on $N$. That is, for each $m \in \{1,2,3\}$ there is a linear order $L_m$ on $N$ with
--   $$
--   \bar E_m \subseteq L_m .
--   $$
--
--   Since $P \subseteq \bar E_m$, every such $L_m$ is a linear extension of $P$; these are the three linear orders of the realizer in Lemma 4.1.
--
--   **Formalization Note** The paper calls $\bar E_m$ "extensions of $P$" and its proof shows that they "do not contain cycles"; the next paragraph takes "any linear extensions of $\bar E_1, \bar E_2, \bar E_3$". The relation $\bar E_2$ itself need not be transitive (with one plus job $j_3$, $l(3)=r(3)=2$: $(j_1,j_2)\in E_2$, $(j_2,j_3)\in P$, but $(j_1,j_3)\in E_1$), so "is a partial order" would be false; the formal statement is the existence of a linear order containing $\bar E_m$, which is equivalent to acyclicity. The numbering assumption is the hypothesis `Monotone C.l`.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 668, Lemma A.2 (numbering assumption from p. 667, Appendix)

import Mathlib
import Definitions.Def_SingleMachinePrec_ConvexBipartite_IncPartition

namespace SingleMachinePrec.ConvexBipartite

open ConvexBipartiteOrder

/-- Lemma A.2 (Ambühl et al. 2011, p. 668). Assume the plus jobs are numbered so that a smaller
plus index has a smaller or equal left end `l` (Appendix, p. 667). Then each of
`Ē₁ = E₁ ∪ P`, `Ē₂ = E₂ ∪ P`, `Ē₃ = E₃ ∪ P` is contained in a linear order on the jobs
("is an extension of P": it contains `P` and has no cycle), i.e. each has a linear extension. -/
theorem lemma_A_2 {a b : ℕ} (C : ConvexBipartiteOrder a b) (hnum : Monotone C.l) :
    (∃ L : Job a b → Job a b → Prop, IsLinearExtension (C.Ebar C.E1) L) ∧
    (∃ L : Job a b → Job a b → Prop, IsLinearExtension (C.Ebar C.E2) L) ∧
    (∃ L : Job a b → Job a b → Prop, IsLinearExtension (C.Ebar C.E3) L) := by sorry

end SingleMachinePrec.ConvexBipartite
