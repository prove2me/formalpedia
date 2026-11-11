-- Prove2me | Theorems.Thm_SingleExpBisect_Main_lemma_3_9
-- name    : SingleExpBisect.Main.lemma_3_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:40:35.37077+00:00
-- url     : https://prove2.me/theorems/5cf8137b-27f7-4a8e-a584-c69362018839
-- title:
--   Lemma 3.9 — every component of G[Φ_t(S)] meets V(G_t) (G connected)
-- statement:
--   For a node $t$ of the Section 3 decomposition $T$ of $G$, every $S\subseteq V(G_t)$ and every connected component $K$ of $G[\Phi_t(S)]$ satisfy $K\cap V(G_t)\ne\emptyset$.
--
--   This is the printed claim, without a connectivity assumption on $G$. The disconnected counterexample is recorded in INSIGHTS.yaml (I1); the mission does not substitute a corrected claim.
--
--   Differences from the source:
--   - reading: T is the decomposition supplied by Theorem 1.1 → IsSec3Decomp G T k: rooted tree decomposition, adhesion at most 2k, bags (2k,k)-edge-unbreakable in G, at most max n 1 nodes, and nonempty bags when n > 0; reason: the setup on p. 15 uses the construction; pp. 23 and 35 bound its number of bags by n and p. 35 puts a vertex in each bag; at n = 0 use one empty bag; the size bound prevents an unbounded decomposition input at fixed n
--   - encoding: K ∈ K_S, a connected component of G[Φ_t(S)] → published IsComponent G (Phi G W S) K; reason: the published definition is a maximal connected subset
-- source:
--   Kumabe, Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New Unbreakable Decomposition, arXiv:2611.05982 (October 2026 version; PDF SHA256 6530ce94…6b76541), §3.4, p. 24, Lemma 3.9 (proof p. 25)

import Mathlib
import Definitions.Def_SingleExpBisect_Main_NodeData
import Definitions.Def_SingleExpBisect_Main_Graphs

open scoped Classical

namespace SingleExpBisect.Main

open MinBisectFPT

/-- Kumabe, *Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New
Unbreakable Decomposition*, arXiv:2611.05982 (October 2026), §3.4, p. 24, Lemma 3.9: for every
`S ⊆ V(G_t)` and every connected component `K` of `G[Φ_t(S)]`, `K ∩ V(G_t) ≠ ∅`.
This states the printed claim in the Section 3 setting, without adding connectivity.
The disconnected counterexample is recorded separately in INSIGHTS.yaml (I1). -/
theorem lemma_3_9 {n : ℕ} (G : SimpleGraph (Fin n)) (T : RootedTD n) (k : ℕ)
    (hT : IsSec3Decomp G T k) (t : Fin T.N)
    (S : Finset (Fin n)) (hS : S ⊆ T.cone t) (K : Finset (Fin n))
    (hK : IsComponent G (Phi G (T.cone t) S) K) :
    (K ∩ T.cone t).Nonempty := by sorry

end SingleExpBisect.Main
