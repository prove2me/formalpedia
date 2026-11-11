-- Prove2me | Theorems.Thm_SnarlSPQR_Snarls_lemma_11
-- name    : SnarlSPQR.Snarls.lemma_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:30:26.094206+00:00
-- url     : https://prove2.me/theorems/3f5e6f11-fc78-4d27-bc3d-78d62d92058e
-- title:
--   Lemma 11 — the snarls of G are exactly the snarls of its sign-cut graphs
-- statement:
--   Let $G$ be a loopless bidirected graph and let $u\alpha,v\beta$ be vertex-sides of $G$ (with $u,v\in V(G)$). Then
--   $$\{u\alpha,v\beta\}\ \text{is a snarl of } G \iff \text{there is a sign-cut graph } F \text{ of } G \text{ such that } \{u\alpha,v\beta\} \text{ is a snarl of } F.$$
--   This reduces the search for snarls to the sign-cut graphs, where tips and non-tips behave separately (Theorem 8). The proof is on pp. 32–33.
--
--   Differences from the source:
--   - reading: G a bidirected graph → G : BiGraph V with G.Valid (every endpoint of an edge is a vertex, no loops); the edges form a Finset, so there are no parallel edges; reason: standing assumptions of §3 (no parallel edges, p. 9) and §5.1 (no loops, p. 28); splitting is only defined for loopless graphs
-- source:
--   Sena, Politov, Moumard, Cairo, Rizzi, Cáceres, Schmidt, Harviainen, Tomescu, Identifying bubble-like subgraphs in linear-time via a unified SPQR-tree framework, arXiv:2604.08071 (copy of 2026-11-03, sha256 40a9dca1…), p. 31, Lemma 11 (proved pp. 32–33)

import Mathlib
import Definitions.Def_SnarlSPQR_Snarls_SignCut

namespace SnarlSPQR.Snarls

/-- Lemma 11 (p. 31, proved pp. 32–33): `{uα, vβ}` is a snarl of `G` if and only if it is a snarl
of some sign-cut graph of `G`. -/
theorem lemma_11 {V : Type} (G : BiGraph V) (hG : G.Valid)
    (a b : V × Sign) (ha : a.1 ∈ G.verts) (hb : b.1 ∈ G.verts) :
    G.Snarl a b ↔ ∃ F : BiGraph V, G.IsSignCut F ∧ F.Snarl a b := by sorry

end SnarlSPQR.Snarls
