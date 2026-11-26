-- Prove2me | Theorems.Thm_SingleExpBisect_Main_lemma_3_10_connected
-- name    : SingleExpBisect.Main.lemma_3_10_connected
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T09:28:38.553566+00:00
-- url     : https://prove2.me/theorems/a64c3452-e906-4c4f-a329-418e69219f1f
-- title:
--   Lemma 3.10 (connected graphs) — connected support of the truncated formal logarithm
-- statement:
--   Let $G$ be connected, let $t$ be a node of the Section 3 decomposition, and let $Z_t$ be its cut generating polynomial with cutoff $k$. Consider a monomial in the vertex variables of the cone and the cut variable $w$. Suppose its coefficient in $\log Z_t$ is nonzero and its $w$-degree is $c\le k$. If $S$ consists of the vertices whose variables have positive exponent, the maximal minimum-cut side $\Phi_t(S)$ induces a connected subgraph of $G$, and its edge boundary has size at most $c$.
--
--   This version makes the connected-input hypothesis explicit. The proof of the main theorem applies the construction separately to connected components.
-- source:
--   Kumabe, Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New Unbreakable Decomposition, arXiv:2611.05982 (October 2026 version; PDF SHA256 6530ce94…6b76541), §3.4, p. 25, Lemma 3.10. Connected-input formulation of the printed statement. https://arxiv.org/abs/2611.05982

import Mathlib
import Definitions.Def_MinBisectFPT_cutSize
import Definitions.Def_SingleExpBisect_Main_NodeData
import Definitions.Def_SingleExpBisect_Main_Graphs

open scoped Classical

namespace SingleExpBisect.Main

open MinBisectFPT

/-- Connected-graph version of Lemma 3.10, with the hypothesis used when Section 3 is applied in the proof of the main theorem. -/
theorem lemma_3_10_connected {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.Connected) (T : RootedTD n) (k : ℕ)
    (hT : IsSec3Decomp G T k) (t : Fin T.N) (c : ℕ) (hc : c ≤ k) (a : Fin n → ℕ)
    (hcoeff : MvPowerSeries.coeff
      (Finsupp.single Var.w c + ∑ v ∈ T.cone t, Finsupp.single (Var.y v) (a v))
      (logPS (Zfull G (T.cone t) k : MvPowerSeries (Var n) ℚ)) ≠ 0) :
    (G.induce (Phi G (T.cone t) ((T.cone t).filter (fun v => 0 < a v)) : Set (Fin n))).Connected ∧
      cutSize G (Phi G (T.cone t) ((T.cone t).filter (fun v => 0 < a v))) ≤ c := by sorry

end SingleExpBisect.Main
