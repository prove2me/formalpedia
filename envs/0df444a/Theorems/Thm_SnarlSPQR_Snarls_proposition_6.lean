-- Prove2me | Theorems.Thm_SnarlSPQR_Snarls_proposition_6
-- name    : SnarlSPQR.Snarls.proposition_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:30:23.484205+00:00
-- url     : https://prove2.me/theorems/87610773-7ffa-47f5-912e-223a5f6a32af
-- title:
--   Proposition 6 — a non-tip of a sign-cut graph has opposite signs inside one block
-- statement:
--   Let $G$ be a loopless bidirected graph, $F$ a sign-cut graph of $G$, and $u\in V(F)$. If $u$ is not a tip of $F$, then some block $B$ of $F$ has vertex-sides of both signs at $u$:
--   $$\exists B\ \text{block of } F:\quad B \text{ has } u+ \text{ and } u-.$$
--
--   Differences from the source:
--   - reading: G a bidirected graph → G : BiGraph V with G.Valid (every endpoint of an edge is a vertex, no loops); the edges form a Finset, so there are no parallel edges; reason: standing assumptions of §3 (no parallel edges, p. 9) and §5.1 (no loops, p. 28); splitting is only defined for loopless graphs
-- source:
--   Sena, Politov, Moumard, Cairo, Rizzi, Cáceres, Schmidt, Harviainen, Tomescu, Identifying bubble-like subgraphs in linear-time via a unified SPQR-tree framework, arXiv:2604.08071 (copy of 2026-11-03, sha256 40a9dca1…), p. 32, Proposition 6

import Mathlib
import Definitions.Def_SnarlSPQR_Snarls_SignCut

namespace SnarlSPQR.Snarls

/-- Proposition 6 (p. 32): a non-tip `u` of a sign-cut graph `F` has vertex-sides of both signs
inside one block of `F`. -/
theorem proposition_6 {V : Type} (G F : BiGraph V) (hG : G.Valid) (hF : G.IsSignCut F)
    (u : V) (hu : u ∈ F.verts) (hnt : ¬ F.IsTip u) :
    ∃ B : BiGraph V, F.IsBlock B ∧ B.HasSide u .pos ∧ B.HasSide u .neg := by sorry

end SnarlSPQR.Snarls
