-- Prove2me | Theorems.Thm_SnarlSPQR_Snarls_proposition_8
-- name    : SnarlSPQR.Snarls.proposition_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:29:03.330351+00:00
-- url     : https://prove2.me/theorems/59354af9-6cc9-4ba6-b369-f0eb9f26e1f8
-- title:
--   Proposition 8 — two internally vertex-disjoint u-v paths in the snarl component give minimality
-- statement:
--   Let $G$ be a loopless bidirected graph and let $\{u\alpha,v\beta\}$ be separable in $G$, with snarl component $X$. If $X$ has two distinct, internally vertex-disjoint undirected $u$-$v$ paths, then $\{u\alpha,v\beta\}$ is a snarl of $G$.
--
--   This is the paper's main tool for proving minimality at P- and R-nodes.
--
--   Differences from the source:
--   - reading: G a bidirected graph → G : BiGraph V with G.Valid (every endpoint of an edge is a vertex, no loops); the edges form a Finset, so there are no parallel edges; reason: standing assumptions of §3 (no parallel edges, p. 9) and §5.1 (no loops, p. 28); splitting is only defined for loopless graphs
--   - encoding: X has two internally vertex-disjoint u-v paths → the underlying undirected graph of the split graph has two distinct internally vertex-disjoint (u,false)-(v,false) paths (TwoDisjointPaths); reason: a path starting at u lies in the component X of u, so the two conditions coincide; paths are vertex/edge sequences, so two parallel edges count as two paths, as the proof (p. 35) does
-- source:
--   Sena, Politov, Moumard, Cairo, Rizzi, Cáceres, Schmidt, Harviainen, Tomescu, Identifying bubble-like subgraphs in linear-time via a unified SPQR-tree framework, arXiv:2604.08071 (copy of 2026-11-03, sha256 40a9dca1…), p. 34, Proposition 8

import Mathlib
import Definitions.Def_SnarlSPQR_Snarls_Snarl

namespace SnarlSPQR.Snarls

/-- Proposition 8 (p. 34): a separable pair `{uα, vβ}` whose snarl component has two internally
vertex-disjoint `u`-`v` paths is a snarl. (The paths of the component of `u` in the split graph are
its paths starting at `u`.) -/
theorem proposition_8 {V : Type} (G : BiGraph V) (hG : G.Valid) (a b : V × Sign)
    (hs : G.Separable a b)
    (hp : (G.split2 a b).U.TwoDisjointPaths (a.1, false) (b.1, false)) :
    G.Snarl a b := by sorry

end SnarlSPQR.Snarls
