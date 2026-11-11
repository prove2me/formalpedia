-- Prove2me | Theorems.Thm_SnarlSPQR_Snarls_lemma_1
-- name    : SnarlSPQR.Snarls.lemma_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:28:20.679313+00:00
-- url     : https://prove2.me/theorems/360ad1c4-188f-4436-af18-51b2dcb3cab3
-- title:
--   Lemma 1 — virtual edges and nonadjacent S-node pairs versus separation and split pairs
-- statement:
--   Let $H$ be an undirected 2-connected multigraph (parallel edges allowed, as in §2.1) and $T$ an SPQR tree of $H$. For each S-node $\mu$, let $X_\mu$ be the set of pairs of nonadjacent vertices of $\mathrm{skeleton}(\mu)$.
--
--   1. **Q-nodes omitted.** The endpoint pairs of the virtual edges over all skeletons, together with $\bigcup_\mu X_\mu$, form exactly the set of separation pairs of $H$.
--   2. **Q-nodes included.** The same union, taken in the tree with Q-nodes, is exactly the set of split pairs of $H$.
--
--   This is stated as printed. Clause 1 fails for multigraphs (see the mission's insight: $H$ with edges $uv,uv,uw,wv$ has a virtual edge $\{u,v\}$ but no separation pair). Only the inclusion "separation pairs $\subseteq$ union" is used for Theorem 2.
--
--   Differences from the source:
--   - reading: T the SPQR tree of H (Q-nodes omitted) → T any tree with H.IsSPQRTree e T, for any reference edge e ∈ E(H); nodes of the Q-less tree are the non-Q subtrees; reason: the recursive definition (pp. 6–8) depends on a reference edge and lists children in no fixed order; the statement is claimed for the SPQR tree whichever is chosen
--   - encoding: the union of the virtual edges over the skeletons (Q-nodes omitted) → the reference pairs ν.refPair of the non-root nodes ν of the Q-less tree; reason: each virtual edge of the Q-less tree joins a node to its non-Q parent and has the endpoints of the child's reference edge; the root's slot 0 is the real edge e
--   - encoding: the same union with Q-nodes included → the reference pairs of all subtrees of T (Q-nodes and the root included; the root's pair is that of the Q-node of e); reason: with Q-nodes every skeleton edge except a Q-node's own real edge is virtual
--   - reading: H an undirected 2-connected graph → H : MGraph V E (a multigraph) with H.WF and H.TwoConnected; reason: §2.1 allows parallel edges and Lemma 1 is applied to U(G) of bidirected graphs, which has them
-- source:
--   Sena, Politov, Moumard, Cairo, Rizzi, Cáceres, Schmidt, Harviainen, Tomescu, Identifying bubble-like subgraphs in linear-time via a unified SPQR-tree framework, arXiv:2604.08071 (copy of 2026-11-03, sha256 40a9dca1…), p. 8, Lemma 1

import Mathlib
import Definitions.Def_SnarlSPQR_Snarls_SPQRTree

namespace SnarlSPQR.Snarls

/-- Lemma 1 (p. 8), as printed (false for multigraphs, see the mission's INSIGHTS): for a
2-connected undirected multigraph `H` and an SPQR tree `T` of `H`, (Q-nodes omitted) the endpoint
pairs of the virtual edges together with the nonadjacent vertex pairs of S-node skeletons are
exactly the separation pairs of `H`; (Q-nodes included) the same union is exactly the set of split
pairs of `H`. -/
theorem lemma_1 {V E : Type} (H : MGraph V E) (hwf : H.WF) (h2 : H.TwoConnected)
    (e : E) (T : Tree V E) (hT : H.IsSPQRTree e T) :
    {p : Sym2 V | (∃ ν, T.IsNode ν ∧ ν ≠ T ∧ p = ν.refPair) ∨
        ∃ μ, T.IsNode μ ∧ μ.kind? = some .S ∧ ∃ a b, p = s(a, b) ∧ μ.NonadjacentInSkel a b} =
      {p | ∃ a b, p = s(a, b) ∧ H.IsSepPair a b} ∧
    {p : Sym2 V | (∃ ν ∈ T.subtrees, p = ν.refPair) ∨
        ∃ μ, T.IsNode μ ∧ μ.kind? = some .S ∧ ∃ a b, p = s(a, b) ∧ μ.NonadjacentInSkel a b} =
      {p | ∃ a b, p = s(a, b) ∧ H.IsSplitPair a b} := by sorry

end SnarlSPQR.Snarls
