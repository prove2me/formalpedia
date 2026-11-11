-- Prove2me | Theorems.Thm_SnarlSPQR_Snarls_lemma_2
-- name    : SnarlSPQR.Snarls.lemma_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:28:14.347403+00:00
-- url     : https://prove2.me/theorems/a6b48ac0-a5f3-417d-82ca-d0ded0eb1289
-- title:
--   Lemma 2 — an SPQR tree has O(|V|) nodes and O(|E|) skeleton edges
-- statement:
--   There is a universal constant $C$ such that, for every biconnected undirected multigraph $H$ (no cutvertex), every reference edge $e$ and every SPQR tree $T$ of $H$ with respect to $e$ (Q-nodes omitted),
--   $$\#\{\text{nodes of } T\}\le C\,|V(H)| \qquad\text{and}\qquad \sum_{\mu\in T}|E(\mathrm{skeleton}(\mu))|\le C\,|E(H)|.$$
--   The paper cites this from Di Battista and Tamassia (1990b). It drives the linear size and time bounds of Theorem 2.
--
--   Differences from the source:
--   - reading: T the SPQR tree of H (Q-nodes omitted) → T any tree with H.IsSPQRTree e T, for any reference edge e ∈ E(H); nodes of the Q-less tree are the non-Q subtrees; reason: the recursive definition (pp. 6–8) depends on a reference edge and lists children in no fixed order; the statement is claimed for the SPQR tree whichever is chosen
--   - reading: O(|V(H)|) nodes and O(|E(H)|) skeleton edges → ∃ C : ℕ, before all types and graphs: nodes ≤ C·|V(H)| and total skeleton edges ≤ C·|E(H)|; reason: O(·) as one universal constant
--   - reading: H = (V, E) an undirected biconnected graph → H : MGraph V E (a multigraph) with H.WF and H.Biconnected (no cutvertex); reason: §2.1 allows parallel edges and defines biconnected as having no cutvertex
-- source:
--   Sena, Politov, Moumard, Cairo, Rizzi, Cáceres, Schmidt, Harviainen, Tomescu, Identifying bubble-like subgraphs in linear-time via a unified SPQR-tree framework, arXiv:2604.08071 (copy of 2026-11-03, sha256 40a9dca1…), p. 8, Lemma 2

import Mathlib
import Definitions.Def_SnarlSPQR_Snarls_SPQRTree

namespace SnarlSPQR.Snarls

/-- Lemma 2 (p. 8; Di Battista and Tamassia 1990b): one universal constant `C` such that for every
biconnected undirected multigraph `H` and every SPQR tree `T` of `H` (Q-nodes omitted), `T` has at
most `C·|V(H)|` nodes and its skeletons have at most `C·|E(H)|` edges in total. -/
theorem lemma_2 :
    ∃ C : ℕ, ∀ {V E : Type} (H : MGraph V E), H.WF → H.Biconnected →
      ∀ (e : E) (T : Tree V E), H.IsSPQRTree e T →
        T.qlessNodes.length ≤ C * H.verts.card ∧
        (T.qlessNodes.map fun μ => μ.slots.length).sum ≤ C * H.edges.card := by sorry

end SnarlSPQR.Snarls
