-- Prove2me | Theorems.Thm_SnarlSPQR_Snarls_theorem_8
-- name    : SnarlSPQR.Snarls.theorem_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:30:16.094197+00:00
-- url     : https://prove2.me/theorems/8469ae1c-38f4-48f5-9520-0402b3f18107
-- title:
--   Theorem 8 — tip pairs of a sign-cut graph are snarls; non-tip snarls are split pairs of a unique block
-- statement:
--   Let $G$ be a loopless bidirected graph and $F$ a sign-cut graph of $G$.
--
--   1. If $u\neq v$ are tips of $F$ with signs $\alpha$ and $\beta$ respectively (all vertex-sides of $F$ at $u$ have sign $\alpha$, all at $v$ have sign $\beta$), then $\{u\alpha,v\beta\}$ is a snarl of $G$.
--   2. If $\{u\alpha,v\beta\}$ is a snarl of $G$ and $u,v\in V(F)$ are non-tips of $F$, then there is exactly one block $B$ of $F$ in which $u$ and $v$ are both non-tips and $\{u,v\}$ is a split pair of $B$ (a separation pair of $U(B)$ or the endpoints of an edge of $B$):
--   $$\exists!\,B:\ B \text{ block of } F,\ u,v \text{ non-tips in } B,\ \{u,v\} \text{ split pair of } B.$$
--
--   Part 1 is why the tips of each sign-cut graph can be stored as one set $T_i$ (all pairs are snarls). Part 2 confines the remaining snarls to the SPQR trees of single blocks. The proof is on pp. 33–34.
--
--   Differences from the source:
--   - reading: G a bidirected graph → G : BiGraph V with G.Valid (every endpoint of an edge is a vertex, no loops); the edges form a Finset, so there are no parallel edges; reason: standing assumptions of §3 (no parallel edges, p. 9) and §5.1 (no loops, p. 28); splitting is only defined for loopless graphs
--   - encoding: u and v are distinct tips in F with signs α, β → u ≠ v ∈ V(F), F.AllSidesAt u α, F.AllSidesAt v β; reason: a tip with sign α is a tip all of whose vertex-sides carry α
-- source:
--   Sena, Politov, Moumard, Cairo, Rizzi, Cáceres, Schmidt, Harviainen, Tomescu, Identifying bubble-like subgraphs in linear-time via a unified SPQR-tree framework, arXiv:2604.08071 (copy of 2026-11-03, sha256 40a9dca1…), p. 31, Theorem 8 (proved pp. 33–34)

import Mathlib
import Definitions.Def_SnarlSPQR_Snarls_SignCut

namespace SnarlSPQR.Snarls

/-- Theorem 8 (p. 31, proved pp. 33–34): (1) two distinct tips `u, v` of a sign-cut graph `F`, with
signs `α, β`, give a snarl `{uα, vβ}` of `G`; (2) if `{uα, vβ}` is a snarl of `G` and `u, v` are
non-tips of `F`, there is a unique block of `F` in which `u` and `v` are non-tips and `{u, v}` is
a split pair. -/
theorem theorem_8 {V : Type} (G F : BiGraph V) (hG : G.Valid) (hF : G.IsSignCut F) :
    (∀ (u v : V) (α β : Sign), u ∈ F.verts → v ∈ F.verts → u ≠ v →
      F.AllSidesAt u α → F.AllSidesAt v β → G.Snarl (u, α) (v, β)) ∧
    (∀ (u v : V) (α β : Sign), G.Snarl (u, α) (v, β) → u ∈ F.verts → v ∈ F.verts →
      ¬ F.IsTip u → ¬ F.IsTip v →
      ∃! B : BiGraph V, F.IsBlock B ∧ ¬ B.IsTip u ∧ ¬ B.IsTip v ∧ B.U.IsSplitPair u v) := by sorry

end SnarlSPQR.Snarls
