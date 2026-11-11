-- Prove2me | Theorems.Thm_SnarlSPQR_Snarls_lemma_3
-- name    : SnarlSPQR.Snarls.lemma_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:28:24.747981+00:00
-- url     : https://prove2.me/theorems/b55b44a1-d5c9-461b-9845-a87bea456acc
-- title:
--   Lemma 3 — inside the expansion of a virtual edge {u, v}, every vertex reaches v avoiding u
-- statement:
--   Let $G$ be a loopless bidirected graph, $H$ a 2-connected subgraph of $G$, and $T$ an SPQR tree of $H$ (Q-nodes omitted). Let $e=\{u,v\}$ be a virtual edge of $\mathrm{skeleton}(\mu)$ for a node $\mu$ of $T$; it pertains to an adjacent node $\nu$, and its expansion is the subgraph of $H$ induced by the real edges on $\nu$'s side of the tree edge $\{\mu,\nu\}$. If $a\in V(H)\setminus\{u\}$ is a vertex of $\mathrm{expansion}(e)$, then
--   $$\mathrm{expansion}(e)-u \ \text{has an undirected } a\text{-}v \text{ path}.$$
--
--   Differences from the source:
--   - reading: G a bidirected graph → G : BiGraph V with G.Valid (every endpoint of an edge is a vertex, no loops); the edges form a Finset, so there are no parallel edges; reason: standing assumptions of §3 (no parallel edges, p. 9) and §5.1 (no loops, p. 28); splitting is only defined for loopless graphs
--   - reading: T the SPQR tree of H (Q-nodes omitted) → T any tree with H.U.IsSPQRTree e T, for any reference edge e ∈ E(H); nodes are the non-Q subtrees; reason: the recursive definition (pp. 6–8) depends on a reference edge and lists children in no fixed order; the statement is claimed for the SPQR tree whichever is chosen
--   - encoding: e = {u, v} a virtual edge of skeleton(μ) and expansion(e) → T.Adjacent μ ν with T.treeEdgePair μ ν = s(u, v); expansion edge set T.sideEdges H.edges ν μ; the path avoiding u is reachability in (expansion − u); reason: a virtual edge of the Q-less tree is a tree edge seen from μ; its expansion is the side of the pertinent node ν (p. 8)
-- source:
--   Sena, Politov, Moumard, Cairo, Rizzi, Cáceres, Schmidt, Harviainen, Tomescu, Identifying bubble-like subgraphs in linear-time via a unified SPQR-tree framework, arXiv:2604.08071 (copy of 2026-11-03, sha256 40a9dca1…), p. 8, Lemma 3

import Mathlib
import Definitions.Def_SnarlSPQR_Snarls_SPQRTree
import Definitions.Def_SnarlSPQR_Snarls_BiGraph

namespace SnarlSPQR.Snarls

/-- Lemma 3 (p. 8): for a virtual edge `{u, v}` of `skeleton(μ)` (pertaining to the adjacent node
`ν`) and a vertex `a ≠ u` of `H` in its expansion, the expansion has an `a`-`v` path avoiding `u`. -/
theorem lemma_3 {V : Type} (G H : BiGraph V) (hG : G.Valid) (hH : G.Is2ConnSub H)
    (e : Sym2 (V × Sign)) (T : Tree V (Sym2 (V × Sign))) (hT : H.U.IsSPQRTree e T)
    (μ ν : Tree V (Sym2 (V × Sign))) (hadj : T.Adjacent μ ν)
    (u v : V) (huv : T.treeEdgePair μ ν = s(u, v))
    (a : V) (ha : a ∈ H.verts) (hau : a ≠ u)
    (hexp : a ∈ (BiGraph.edgeInduced (T.sideEdges H.edges ν μ)).verts) :
    ((BiGraph.edgeInduced (T.sideEdges H.edges ν μ)).U.deleteVert u).Reach a v := by sorry

end SnarlSPQR.Snarls
