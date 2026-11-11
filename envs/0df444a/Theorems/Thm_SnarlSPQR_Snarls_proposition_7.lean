-- Prove2me | Theorems.Thm_SnarlSPQR_Snarls_proposition_7
-- name    : SnarlSPQR.Snarls.proposition_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:30:38.809197+00:00
-- url     : https://prove2.me/theorems/05360141-d4d0-4a9e-ad04-5d81b1a9e391
-- title:
--   Proposition 7 — a tip and a non-tip of a sign-cut graph are never separable
-- statement:
--   Let $G$ be a loopless bidirected graph and $F$ a sign-cut graph of $G$ with vertices $u,v$. Suppose $u$ is a tip of $F$ with sign $\alpha$ (every vertex-side of $F$ at $u$ has sign $\alpha$) and $v$ is a non-tip of $F$. Then for both signs $\beta$,
--   $$\{u\alpha,v\beta\}\ \text{is not separable in } F.$$
--
--   Differences from the source:
--   - reading: G a bidirected graph → G : BiGraph V with G.Valid (every endpoint of an edge is a vertex, no loops); the edges form a Finset, so there are no parallel edges; reason: standing assumptions of §3 (no parallel edges, p. 9) and §5.1 (no loops, p. 28); splitting is only defined for loopless graphs
--   - encoding: u is a tip with sign α → F.AllSidesAt u α: every vertex-side of F at u has sign α; reason: a tip all of whose vertex-sides carry α; this implies u is a tip
-- source:
--   Sena, Politov, Moumard, Cairo, Rizzi, Cáceres, Schmidt, Harviainen, Tomescu, Identifying bubble-like subgraphs in linear-time via a unified SPQR-tree framework, arXiv:2604.08071 (copy of 2026-11-03, sha256 40a9dca1…), p. 32, Proposition 7

import Mathlib
import Definitions.Def_SnarlSPQR_Snarls_SignCut

namespace SnarlSPQR.Snarls

/-- Proposition 7 (p. 32): in a sign-cut graph `F`, a tip `u` with sign `α` and a non-tip `v` never
form a separable pair `{uα, vβ}` (separability in `F`). -/
theorem proposition_7 {V : Type} (G F : BiGraph V) (hG : G.Valid) (hF : G.IsSignCut F)
    (u v : V) (hu : u ∈ F.verts) (hv : v ∈ F.verts) (α : Sign)
    (htip : F.AllSidesAt u α) (hnt : ¬ F.IsTip v) (β : Sign) :
    ¬ F.Separable (u, α) (v, β) := by sorry

end SnarlSPQR.Snarls
