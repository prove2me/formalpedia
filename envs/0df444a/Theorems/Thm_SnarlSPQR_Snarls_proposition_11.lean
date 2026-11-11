-- Prove2me | Theorems.Thm_SnarlSPQR_Snarls_proposition_11
-- name    : SnarlSPQR.Snarls.proposition_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:31:05.673681+00:00
-- url     : https://prove2.me/theorems/7b92a9e7-eb85-43da-b04e-8813a1477af2
-- title:
--   Proposition 11 — sign-split tree edges at an R-node give snarls
-- statement:
--   Let $G$ be a loopless bidirected graph, $H$ a maximal 2-connected subgraph of $G$, $T$ an SPQR tree of $H$ (Q-nodes omitted), and $\nu,\mu$ adjacent nodes of $T$ with $\nu$ an R-node. Let $e_\mu=\{u,v\}$ be the virtual edge of $\mathrm{skeleton}(\nu)$ pertaining to $\mu$, and $e_\nu=\{u,v\}$ the virtual edge of $\mathrm{skeleton}(\mu)$ pertaining to $\nu$. Let $\alpha,\beta$ be signs. Suppose:
--   - all vertex-sides at $u$ and $v$ in $\mathrm{expansion}(e_\nu)$ have signs $\alpha$ and $\beta$ respectively;
--   - all vertex-sides at $u$ and $v$ in $\mathrm{expansion}(e_\mu)$ have signs $\hat\alpha$ and $\hat\beta$ respectively;
--   - neither $u$ nor $v$ has a dangling block with respect to $H$.
--
--   Then $\{u\alpha,v\beta\}$ is a snarl of $G$.
--
--   Differences from the source:
--   - reading: G a bidirected graph → G : BiGraph V with G.Valid (every endpoint of an edge is a vertex, no loops); the edges form a Finset, so there are no parallel edges; reason: standing assumptions of §3 (no parallel edges, p. 9) and §5.1 (no loops, p. 28); splitting is only defined for loopless graphs
--   - reading: T the SPQR tree of H (Q-nodes omitted) → T any tree with H.U.IsSPQRTree e T, for any reference edge e ∈ E(H); nodes are the non-Q subtrees; reason: the recursive definition (pp. 6–8) depends on a reference edge and lists children in no fixed order; the statement is claimed for the SPQR tree whichever is chosen
--   - encoding: a virtual edge e_μ = {u, v} of skeleton(ν) pertaining to μ, and its expansion → adjacent nodes ν, μ of the Q-less tree (T.Adjacent), endpoints T.treeEdgePair = s(u, v), expansion edge set T.sideEdges H.edges μ ν (the real edges on μ's side); reason: a virtual edge of the Q-less tree is exactly a tree edge seen from one end; its expansion is defined from the two subtrees (p. 8)
-- source:
--   Sena, Politov, Moumard, Cairo, Rizzi, Cáceres, Schmidt, Harviainen, Tomescu, Identifying bubble-like subgraphs in linear-time via a unified SPQR-tree framework, arXiv:2604.08071 (copy of 2026-11-03, sha256 40a9dca1…), p. 37, Proposition 11

import Mathlib
import Definitions.Def_SnarlSPQR_Snarls_GoodVertex

namespace SnarlSPQR.Snarls

/-- Proposition 11 (p. 37): for adjacent nodes `ν, μ` with `ν` an R-node, the tree edge with
endpoints `{u, v}`, all vertex-sides at `u, v` in `expansion(e_ν)` (the side of `ν`) of signs
`α, β`, all those in `expansion(e_μ)` (the side of `μ`) of signs `α̂, β̂`, and no dangling blocks at
`u, v` with respect to `H`, the pair `{uα, vβ}` is a snarl. -/
theorem proposition_11 {V : Type} (G H : BiGraph V) (hG : G.Valid) (hH : G.IsMax2Conn H)
    (e : Sym2 (V × Sign)) (T : Tree V (Sym2 (V × Sign))) (hT : H.U.IsSPQRTree e T)
    (ν μ : Tree V (Sym2 (V × Sign))) (hadj : T.Adjacent ν μ) (hR : ν.kind? = some .R)
    (u v : V) (huv : T.treeEdgePair ν μ = s(u, v)) (α β : Sign)
    (hνu : (BiGraph.edgeInduced (T.sideEdges H.edges ν μ)).AllSidesAt u α)
    (hνv : (BiGraph.edgeInduced (T.sideEdges H.edges ν μ)).AllSidesAt v β)
    (hμu : (BiGraph.edgeInduced (T.sideEdges H.edges μ ν)).AllSidesAt u α.opp)
    (hμv : (BiGraph.edgeInduced (T.sideEdges H.edges μ ν)).AllSidesAt v β.opp)
    (hdu : ¬ G.HasDangling H u) (hdv : ¬ G.HasDangling H v) :
    G.Snarl (u, α) (v, β) := by sorry

end SnarlSPQR.Snarls
