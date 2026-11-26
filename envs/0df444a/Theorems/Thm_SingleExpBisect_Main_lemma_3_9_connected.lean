-- Prove2me | Theorems.Thm_SingleExpBisect_Main_lemma_3_9_connected
-- name    : SingleExpBisect.Main.lemma_3_9_connected
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T09:22:55.083321+00:00
-- url     : https://prove2.me/theorems/b82e2a41-c8d2-512d-9678-c1ca4fe91ac7
-- title:
--   Lemma 3.9 (connected graphs) — every component of the extremal cut side meets the cone
-- statement:
--   Let $G$ be a connected graph and let $t$ be a node of its Section 3 tree decomposition. Fix a set $S$ of vertices in the cone of $t$. Among all cuts whose chosen side meets the cone in exactly $S$, let $\Phi_t(S)$ be the maximal minimum-cut side. Every connected component of the subgraph induced by $\Phi_t(S)$ contains a vertex in the cone of $t$.
--
--   This version makes the connected-input hypothesis explicit. The proof of the main theorem applies the construction separately to connected components.
-- source:
--   Kumabe, Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New Unbreakable Decomposition, arXiv:2611.05982 (October 2026 version; PDF SHA256 6530ce94…6b76541), §3.4, p. 24, Lemma 3.9 (proof p. 25). Connected-input formulation of the printed statement. https://arxiv.org/abs/2611.05982

import Mathlib
import Definitions.Def_SingleExpBisect_Main_NodeData
import Definitions.Def_SingleExpBisect_Main_Graphs

open scoped Classical

namespace SingleExpBisect.Main

open MinBisectFPT

/-- Connected-graph version of Lemma 3.9, with the hypothesis used when Section 3 is applied in the proof of the main theorem. -/
theorem lemma_3_9_connected {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.Connected) (T : RootedTD n) (k : ℕ)
    (hT : IsSec3Decomp G T k) (t : Fin T.N)
    (S : Finset (Fin n)) (hS : S ⊆ T.cone t) (K : Finset (Fin n))
    (hK : IsComponent G (Phi G (T.cone t) S) K) :
    (K ∩ T.cone t).Nonempty := by sorry

end SingleExpBisect.Main
