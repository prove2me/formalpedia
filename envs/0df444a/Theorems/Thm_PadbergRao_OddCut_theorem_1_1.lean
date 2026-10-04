-- Prove2me | Theorems.Thm_PadbergRao_OddCut_theorem_1_1
-- name    : PadbergRao.OddCut.theorem_1_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T23:08:44.613717+00:00
-- url     : https://prove2.me/theorems/8d1350e4-28b8-4eae-902b-e88e7cab09bf
-- title:
--   Theorem 1.1 — a minimum-weight odd-splitting edge of the Gomory–Hu cut-tree defines an odd minimum cut-set
-- statement:
--   Let $G = (V, E)$ be a finite undirected graph without loops and multiple edges, with edge weights $c_e \ge 0$, whose nodes are labelled odd and even such that the set $V_1$ of odd nodes is nonempty and the total label of $G$ is even ($|V_1|$ even). Let $G_T = (N, F)$ be the Gomory–Hu cut-tree of $G$ for all pairs of odd nodes, with edge weights $d_f$. Call a tree edge $f$ **odd-splitting** if its removal decomposes $G_T$ into two subtrees of odd cardinality. Then:
--
--   1. $G_T$ has at least one odd-splitting edge; and
--   2. if $f^* = [r, s]$ is an odd-splitting edge of minimum weight among all odd-splitting edges, and $M$ is the node set of $G$ corresponding to the subtree containing $r$ after removing $f^*$, then $(M : V - M)$ is an odd minimum cut-set:
--
--   $$
--   c(M : V - M) \;=\; \min\{\, c(U : V - U) : U \subseteq V,\ \lambda(U) \text{ odd} \,\}.
--   $$
--
--   Thus the odd minimum cut-set problem is solved by one Gomory–Hu computation on the odd nodes, followed by a search over the edges of the tree.
--
--   Since $|N| = |V_1|$ is even, one of the two subtrees has odd cardinality exactly when the other has, so the statement checks the parity of the $r$-side subtree only.
--
--   **Formalization Note** The cut-tree is `IsOddCutTree c odd H π` (tree nodes identified with odd nodes; Gomory–Hu minimality for every tree edge); the conclusion `IsOddMinCut` minimizes over every node set $U$ with $\lambda(U)$ odd, not only over shores of tree edges. Part 1 ensures that part 2 is not vacuous.
-- source:
--   Padberg, Rao, Odd Minimum Cut-Sets and b-Matchings, Math. Oper. Res. 7 (1982), p. 70, Theorem 1.1

import Mathlib
import Definitions.Def_PadbergRao_OddCut_cutCapacity
import Definitions.Def_PadbergRao_OddCut_IsOddMinCut
import Definitions.Def_PadbergRao_OddCut_IsOddCutTree

namespace PadbergRao.OddCut

/-- Theorem 1.1 (Padberg–Rao 1982, p. 70). Let `G_T` be a Gomory–Hu cut-tree of `G` for the odd
nodes. (1) Some edge of `G_T` splits it into two subtrees of odd cardinality; (2) every such edge
of minimum weight among them defines an odd minimum cut-set of `G`. Since `|V₁|` is even, the
`s`-side subtree has odd cardinality iff the `r`-side one does, so one parity condition suffices. -/
theorem theorem_1_1 {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (hc_symm : ∀ i j, c i j = c j i) (hc_nonneg : ∀ i j, 0 ≤ c i j)
    (odd : Finset V) (hodd_ne : odd.Nonempty) (hodd_even : Even odd.card)
    (H : SimpleGraph {v // v ∈ odd}) (π : V → {v // v ∈ odd})
    (hT : IsOddCutTree c odd H π) :
    (∃ r s : {v // v ∈ odd}, H.Adj r s ∧ Odd (subtree H r s).card) ∧
    ∀ r s : {v // v ∈ odd}, H.Adj r s → Odd (subtree H r s).card →
      (∀ r' s' : {v // v ∈ odd}, H.Adj r' s' → Odd (subtree H r' s').card →
        treeEdgeWeight c H π r s ≤ treeEdgeWeight c H π r' s') →
      IsOddMinCut c odd (shore H π r s) := by sorry

end PadbergRao.OddCut
