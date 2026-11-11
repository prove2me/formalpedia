-- Prove2me | Theorems.Thm_SnarlSPQR_Snarls_proposition_12
-- name    : SnarlSPQR.Snarls.proposition_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:31:14.235148+00:00
-- url     : https://prove2.me/theorems/f05272c1-af9a-4176-a788-32a386cabf5e
-- title:
--   Proposition 12 — opposite signs at u inside an R-node expansion destroy separability
-- statement:
--   Let $G$ be a loopless bidirected graph, $H$ a 2-connected subgraph of $G$, and $T$ an SPQR tree of $H$ (Q-nodes omitted). Let $\nu$ be a node of $T$ whose skeleton has a virtual edge $e_\mu=\{u,v\}$ pertaining to an R-node $\mu$. If $\mathrm{expansion}(e_\mu)$ has vertex-sides of both signs at $u$, then for all signs $\alpha,\beta$,
--   $$\{u\alpha,v\beta\}\ \text{is not separable in } G.$$
--
--   Differences from the source:
--   - reading: G a bidirected graph → G : BiGraph V with G.Valid (every endpoint of an edge is a vertex, no loops); the edges form a Finset, so there are no parallel edges; reason: standing assumptions of §3 (no parallel edges, p. 9) and §5.1 (no loops, p. 28); splitting is only defined for loopless graphs
--   - reading: T the SPQR tree of H (Q-nodes omitted) → T any tree with H.U.IsSPQRTree e T, for any reference edge e ∈ E(H); nodes are the non-Q subtrees; reason: the recursive definition (pp. 6–8) depends on a reference edge and lists children in no fixed order; the statement is claimed for the SPQR tree whichever is chosen
--   - encoding: a virtual edge e_μ = {u, v} of skeleton(ν) pertaining to μ, and its expansion → adjacent nodes ν, μ of the Q-less tree (T.Adjacent), endpoints T.treeEdgePair = s(u, v), expansion edge set T.sideEdges H.edges μ ν (the real edges on μ's side); reason: a virtual edge of the Q-less tree is exactly a tree edge seen from one end; its expansion is defined from the two subtrees (p. 8)
-- source:
--   Sena, Politov, Moumard, Cairo, Rizzi, Cáceres, Schmidt, Harviainen, Tomescu, Identifying bubble-like subgraphs in linear-time via a unified SPQR-tree framework, arXiv:2604.08071 (copy of 2026-11-03, sha256 40a9dca1…), p. 38, Proposition 12

import Mathlib
import Definitions.Def_SnarlSPQR_Snarls_GoodVertex

namespace SnarlSPQR.Snarls

/-- Proposition 12 (p. 38): if the expansion of the virtual edge `e_μ = {u, v}` of `skeleton(ν)`
pertaining to an R-node `μ` has vertex-sides of opposite signs at `u`, then `{uα, vβ}` is not
separable in `G`, for any signs. -/
theorem proposition_12 {V : Type} (G H : BiGraph V) (hG : G.Valid) (hH : G.Is2ConnSub H)
    (e : Sym2 (V × Sign)) (T : Tree V (Sym2 (V × Sign))) (hT : H.U.IsSPQRTree e T)
    (ν μ : Tree V (Sym2 (V × Sign))) (hadj : T.Adjacent ν μ) (hR : μ.kind? = some .R)
    (u v : V) (huv : T.treeEdgePair ν μ = s(u, v))
    (hopp : (BiGraph.edgeInduced (T.sideEdges H.edges μ ν)).HasSide u .pos ∧
      (BiGraph.edgeInduced (T.sideEdges H.edges μ ν)).HasSide u .neg)
    (α β : Sign) :
    ¬ G.Separable (u, α) (v, β) := by sorry

end SnarlSPQR.Snarls
