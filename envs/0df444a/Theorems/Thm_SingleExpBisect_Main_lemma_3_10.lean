-- Prove2me | Theorems.Thm_SingleExpBisect_Main_lemma_3_10
-- name    : SingleExpBisect.Main.lemma_3_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:40:55.292387+00:00
-- url     : https://prove2.me/theorems/ac22bfab-615f-492c-ab18-4aa2affa666f
-- title:
--   Lemma 3.10 — a nonzero coefficient of log Z_t forces Φ_t(S) connected with |δ_G(Φ_t(S))| ≤ c (G connected)
-- statement:
--   For a node $t$ of the Section 3 decomposition $T$ of $G$, let $c\le k$ and $a:V(G)\to\mathbb N$. If the coefficient of $w^c\prod_{v\in V(G_t)}y_v^{a_v}$ in $\log Z_t(y,w)$ is nonzero, then for $S:=\{v\in V(G_t):a_v>0\}$ the graph $G[\Phi_t(S)]$ is connected and $|\delta_G(\Phi_t(S))|\le c$.
--
--   This is the printed claim, without a connectivity assumption on $G$. The disconnected counterexample is recorded in INSIGHTS.yaml (I1); the mission does not substitute a corrected claim.
--
--   Differences from the source:
--   - reading: T is the decomposition supplied by Theorem 1.1 → IsSec3Decomp G T k: rooted tree decomposition, adhesion at most 2k, bags (2k,k)-edge-unbreakable in G, at most max n 1 nodes, and nonempty bags when n > 0; reason: the setup on p. 15 uses the construction; pp. 23 and 35 bound its number of bags by n and p. 35 puts a vertex in each bag; at n = 0 use one empty bag; the size bound prevents an unbounded decomposition input at fixed n
--   - encoding: log Z_t(y, w) in Q[[y, w]]; "Φ_t(S) is connected" → logPS of Zfull G W k as an MvPowerSeries; (G.induce Φ).Connected, which includes nonemptiness; reason: log Z_t has no monomial with empty y-support (its constant is 1 and µ_t(∅) = 0), so S ≠ ∅ under the hypothesis and Φ_t(S) ⊇ S is nonempty
-- source:
--   Kumabe, Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New Unbreakable Decomposition, arXiv:2611.05982 (October 2026 version; PDF SHA256 6530ce94…6b76541), §3.4, p. 25, Lemma 3.10

import Mathlib
import Definitions.Def_MinBisectFPT_cutSize
import Definitions.Def_SingleExpBisect_Main_NodeData
import Definitions.Def_SingleExpBisect_Main_Graphs

open scoped Classical

namespace SingleExpBisect.Main

open MinBisectFPT

/-- Kumabe, *Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New
Unbreakable Decomposition*, arXiv:2611.05982 (October 2026), §3.4, p. 25, Lemma 3.10: if `c ≤ k`
and the coefficient of `w^c Π_{v ∈ V(G_t)} y_v^{a_v}` in `log Z_t(y, w)` is nonzero, then for
`S := {v ∈ V(G_t) : a_v > 0}` the set `Φ_t(S)` is connected and `|δ_G(Φ_t(S))| ≤ c`.
This states the printed claim without adding connectivity of `G`; see INSIGHTS.yaml (I1). -/
theorem lemma_3_10 {n : ℕ} (G : SimpleGraph (Fin n)) (T : RootedTD n) (k : ℕ)
    (hT : IsSec3Decomp G T k) (t : Fin T.N) (c : ℕ) (hc : c ≤ k) (a : Fin n → ℕ)
    (hcoeff : MvPowerSeries.coeff
      (Finsupp.single Var.w c + ∑ v ∈ T.cone t, Finsupp.single (Var.y v) (a v))
      (logPS (Zfull G (T.cone t) k : MvPowerSeries (Var n) ℚ)) ≠ 0) :
    (G.induce (Phi G (T.cone t) ((T.cone t).filter (fun v => 0 < a v)) : Set (Fin n))).Connected ∧
      cutSize G (Phi G (T.cone t) ((T.cone t).filter (fun v => 0 < a v))) ≤ c := by sorry

end SingleExpBisect.Main
