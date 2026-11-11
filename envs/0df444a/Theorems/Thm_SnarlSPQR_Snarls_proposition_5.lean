-- Prove2me | Theorems.Thm_SnarlSPQR_Snarls_proposition_5
-- name    : SnarlSPQR.Snarls.proposition_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:30:00.856749+00:00
-- url     : https://prove2.me/theorems/fa7e7e42-38c7-46bf-b52b-7066cba44206
-- title:
--   Proposition 5 — a dangling block at u or v destroys separability
-- statement:
--   Let $G$ be a loopless bidirected graph, let $H$ be a block of $G$, and let $u,v\in V(H)$. If $u$ or $v$ has a dangling block with respect to $H$ (another block of $G$ at that vertex with vertex-sides of both signs there), then for all signs $\alpha,\beta\in\{+,-\}$,
--   $$\{u\alpha,v\beta\}\ \text{is not separable in } G.$$
--   This excludes most non-tip configurations in the search for snarls inside a block.
--
--   Differences from the source:
--   - reading: G a bidirected graph → G : BiGraph V with G.Valid (every endpoint of an edge is a vertex, no loops); the edges form a Finset, so there are no parallel edges; reason: standing assumptions of §3 (no parallel edges, p. 9) and §5.1 (no loops, p. 28); splitting is only defined for loopless graphs
-- source:
--   Sena, Politov, Moumard, Cairo, Rizzi, Cáceres, Schmidt, Harviainen, Tomescu, Identifying bubble-like subgraphs in linear-time via a unified SPQR-tree framework, arXiv:2604.08071 (copy of 2026-11-03, sha256 40a9dca1…), p. 31, Proposition 5

import Mathlib
import Definitions.Def_SnarlSPQR_Snarls_SignCut

namespace SnarlSPQR.Snarls

/-- Proposition 5 (p. 31): if `u` or `v` has a dangling block with respect to the block `H`, then
`{uα, vβ}` is not separable, for any signs. -/
theorem proposition_5 {V : Type} (G H : BiGraph V) (hG : G.Valid) (hH : G.IsBlock H)
    (u v : V) (hu : u ∈ H.verts) (hv : v ∈ H.verts)
    (hd : G.HasDangling H u ∨ G.HasDangling H v) (α β : Sign) :
    ¬ G.Separable (u, α) (v, β) := by sorry

end SnarlSPQR.Snarls
