-- Prove2me | Theorems.Thm_PadbergRao_OddCut_min_tree_edge_min_odd_pair_cut
-- name    : PadbergRao.OddCut.min_tree_edge_min_odd_pair_cut
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T23:03:59.172833+00:00
-- url     : https://prove2.me/theorems/08702b4a-0612-4010-b450-4e11eb31ee6e
-- title:
--   Section 1, p. 70 — a minimum-weight cut-tree edge gives a minimum cut-set for all pairs of odd nodes
-- statement:
--   Let $G = (V, E)$ be a finite undirected graph with edge weights $c_e \ge 0$, and let $V_1$ be a nonempty set of odd-labelled nodes with $|V_1|$ even. Let $G_T = (N, F)$ be a Gomory–Hu cut-tree of $G$ for the odd nodes, with edge weights $d_f$. Let $f^* = [r, s] \in F$ be an edge of minimum weight,
--
--   $$
--   d_{f^*} \;=\; \min\{\, d_f : f \in F \,\},
--   $$
--
--   and let $M$ be the node set of $G$ corresponding to the subtree containing $r$ after $f^*$ is removed. Then $(M : V - M)$ is a minimum cut-set with respect to all pairs of odd nodes in $G$.
--
--   The minimum is taken over all tree edges, with no parity condition. This is the bridge that lets Lemma 1.1 be applied to the cut-tree.
--
--   **Formalization Note** The cut-tree is `IsOddCutTree c odd H π`; $M$ is `shore H π r s` and $d_f$ is `treeEdgeWeight`. Minimality of $f^*$ is stated against every ordered adjacent pair `r' s'`.
-- source:
--   Padberg, Rao, Odd Minimum Cut-Sets and b-Matchings, Math. Oper. Res. 7 (1982), p. 70, Section 1 (unnumbered claim before Theorem 1.1)

import Mathlib
import Definitions.Def_PadbergRao_OddCut_cutCapacity
import Definitions.Def_PadbergRao_OddCut_IsMinOddPairCut
import Definitions.Def_PadbergRao_OddCut_IsOddCutTree

namespace PadbergRao.OddCut

/-- Section 1, p. 70 (Padberg–Rao 1982). Removing a minimum-weight edge `f* = [r, s]` of the
cut-tree `G_T` (minimum over all tree edges) yields a set `M` such that `(M : V − M)` is a
minimum cut-set with respect to all pairs of odd nodes of `G`. -/
theorem min_tree_edge_min_odd_pair_cut {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (hc_symm : ∀ i j, c i j = c j i) (hc_nonneg : ∀ i j, 0 ≤ c i j)
    (odd : Finset V) (hodd_ne : odd.Nonempty) (hodd_even : Even odd.card)
    (H : SimpleGraph {v // v ∈ odd}) (π : V → {v // v ∈ odd})
    (hT : IsOddCutTree c odd H π)
    (r s : {v // v ∈ odd}) (hrs : H.Adj r s)
    (hmin : ∀ r' s' : {v // v ∈ odd}, H.Adj r' s' →
      treeEdgeWeight c H π r s ≤ treeEdgeWeight c H π r' s') :
    IsMinOddPairCut c odd (shore H π r s) := by sorry

end PadbergRao.OddCut
