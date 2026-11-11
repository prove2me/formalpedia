-- Prove2me | Theorems.Thm_SnarlSPQR_Snarls_theorem_2
-- name    : SnarlSPQR.Snarls.theorem_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:30:31.309608+00:00
-- url     : https://prove2.me/theorems/c9114ad0-b8b4-49fb-b14c-518f7026cd78
-- title:
--   Theorem 2 — all snarls of a bidirected graph have an O(|V|)-size representation computable in O(|V|+|E|) time
-- statement:
--   There are one deterministic word-RAM program $P$ and one universal constant $C$ (both fixed before the graph) with the following property. Let $G$ be any finite loopless bidirected graph on the vertices $0,\dots,n-1$; it need not be connected, and its underlying graph may have parallel edges. Let its $m=|E(G)|$ edges be listed in any order and orientation. Then the run of $P$ on the encoding $[n,m,u_1,a_1,v_1,b_1,\dots]$ satisfies:
--   - it halts after at most $C\,(|V(G)|+|E(G)|)+C$ unit-cost steps;
--   - every register stays within $O(\log(|V(G)|+|E(G)|))$ bits;
--   - its output encodes sets $T_1,\dots,T_k$ of vertex-sides and pairs $S_1,\dots,S_\ell$ of vertex-sides forming a representation of the set of all snarls of $G$.
--
--   The representation has the following parts.
--   1. Each $T_i$ is a set of vertex-sides of $G$, and any two distinct vertex-sides in $T_i$ form a snarl of $G$.
--   2. Each $S_j$ is a pair $\{u\alpha,v\beta\}$ that is a snarl of $G$.
--   3. Completeness: every snarl of $G$ is a pair of distinct elements of some $T_i$ or equals some $S_j$.
--   4. Size:
--   $$\sum_{i=1}^{k}|T_i|\le C\,|V(G)|,\qquad \sum_{j=1}^{\ell}|S_j|\le C\,|V(G)|.$$
--
--   A graph can have $\Theta(|V|^2)$ snarls, so a list of snarls cannot be produced in linear time. The sets $T_i$ (the tips of each sign-cut graph) compress the quadratic part. Proof: pp. 38–42, through Theorem 9 and Algorithms 5–9.
--
--   Differences from the source:
--   - reading: G a bidirected graph → G : BiGraph V with G.Valid (every endpoint of an edge is a vertex, no loops); the edges form a Finset, so there are no parallel edges; reason: standing assumptions of §3 (no parallel edges, p. 9) and §5.1 (no loops, p. 28); splitting is only defined for loopless graphs
--   - reading: Given a bidirected graph G … computed in time O(|V(G)| + |E(G)|) → one deterministic CongruencyTU program P (no coin, no query) and constants C, width fixed before G; on encInput n l the run is WordBounded by width·(1 + log₂(2 + n + m)) and halts with cost ≤ C·(n + m) + C; reason: the paper names no machine model; a word RAM with logarithmic words is the standard reading, and the word bound keeps unit-cost arithmetic honest; O(·) as one universal constant, + C for the empty graph
--   - reading: a representation of the set of all snarls of G → IsSnarlRep: items 1–2 plus completeness (every snarl is a pair of distinct elements of some T_i or equals some S_j); reason: 'representation of the set of all snarls' means the represented set is exactly the snarls; without completeness the empty output would satisfy items 1–3
--   - reading: any pair of vertex-sides in T_i identifies a snarl → any two distinct vertex-sides a ≠ b of T_i form a snarl; reason: a snarl needs two vertex-sides; the T_i of Algorithm 9 hold the tips of a sign-cut graph
--   - encoding: G a bidirected graph; output sets T_i, S_j → G : BiGraph (Fin n) with G.verts = univ, given as an edge list l (each edge once, either orientation, any order); output encRep Ts Ss with each T_i a duplicate-free list and S_j an ordered pair compared as an unordered pair; Σ|S_j| = 2ℓ; reason: input and output layouts of the machine; every finite graph is isomorphic to one on Fin n and snarls are invariant under renaming
-- source:
--   Sena, Politov, Moumard, Cairo, Rizzi, Cáceres, Schmidt, Harviainen, Tomescu, Identifying bubble-like subgraphs in linear-time via a unified SPQR-tree framework, arXiv:2604.08071 (copy of 2026-11-03, sha256 40a9dca1…), p. 12, Theorem 2 (restated p. 41; proof pp. 38–42 via Theorem 9 and Algorithms 5–9)

import Mathlib
import Definitions.Def_SnarlSPQR_Snarls_Machine

namespace SnarlSPQR.Snarls

/-- Theorem 2 (p. 12, proved pp. 41–42): one deterministic word-RAM program `P` and one universal
constant `C` such that, for every loopless bidirected graph `G` on the vertices `0, …, n − 1` and
every listing of its edges, the run of `P` on the encoded input halts after at most
`C·(|V(G)| + |E(G)|) + C` steps with words of `O(log(|V(G)| + |E(G)|))` bits, and outputs a
representation `T₁, …, T_k`, `S₁, …, S_ℓ` of the set of all snarls of `G` with
`Σ|T_i| ≤ C·|V(G)|` and `Σ|S_j| ≤ C·|V(G)|`. -/
theorem theorem_2 :
    ∃ (P : CongruencyTU.Program) (C width : ℕ), Deterministic P ∧
      ∀ (n : ℕ) (G : BiGraph (Fin n)), G.verts = Finset.univ → G.Valid →
      ∀ l : List ((Fin n × Sign) × (Fin n × Sign)), IsEdgeListOf G l →
        WordBounded P (encInput n l) width (n + G.edges.card) ∧
        HaltsWithin P (encInput n l) (C * (n + G.edges.card) + C) (fun out =>
          ∃ (Ts : List (List (Fin n × Sign))) (Ss : List ((Fin n × Sign) × (Fin n × Sign))),
            out = encRep Ts Ss ∧ IsSnarlRep G Ts Ss ∧
            (Ts.map List.length).sum ≤ C * n ∧ 2 * Ss.length ≤ C * n) := by sorry

end SnarlSPQR.Snarls
