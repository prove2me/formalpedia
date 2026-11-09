-- Prove2me | Theorems.Thm_PivotADO_OneHop_claim_1_3
-- name    : PivotADO.OneHop.claim_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:15:25.590933+00:00
-- url     : https://prove2.me/theorems/bc591477-29e4-4c79-b599-db906d0c1e89
-- title:
--   Claim 1.3 — a hop receives at most 2(kc+1)(d−1)^(2t) pairs
-- statement:
--   Let $G$ be a finite $d$-regular graph of finite girth $g$, with $n=|V|$, $d\ge3$, integer $r\ge1$, and real $k\ge1$. Fix any $r$-pivot 1-hop $k$-stretch oracle $(H,\mathcal P)$ and any fixed reversal-consistent shortest-path system $P$. Set $c=\lfloor g/(k+1)\rfloor-1$ and $t=1+\lceil\log_{d-1}(4r)\rceil$, and assume the source's standing large-distance condition $c\ge2t+1$.
--
--   For any unordered edge $e\in E_H$, let $\mathcal C_e$ consist of the non-aligned pairs admitting a realizing pivot pair whose unordered hop is $e$. Then
--
--   $$|\mathcal C_e|\le2(kc+1)(d-1)^{2t}.$$
--
--   The right-hand side is a real number; $kc$ is not rounded to an integer. All realizing choices are permitted in this relation, so it bounds any single choice of a realizing walk for each pair. The exact multiplicative constant $2$ and exponent $2t$ are retained.
--
--   Differences from the source:
--   - encoding: a finite vertex set V → an arbitrary Fintype V with classical equality and adjacency decisions; reason: finite relabeling and decidability choices change no graph
--   - encoding: finite girth g and shortest-path distance, infinite between components → G.egirth = (g : ℕ∞) and G.edist; weighted distances use ENat.toENNReal; reason: acyclic and disconnected inputs retain their infinite values
--   - generalization: finite nonnegative edge weights → edge weights in ℝ≥0∞, including infinity; reason: an infinite-weight stored edge is counted and cannot improve any finite query; finite-weight oracles are included
--   - encoding: c = floor(g/(k+1))-1 and t = 1+ceil(log base d-1 of 4r) → pairDistance g k and alignmentDepth d r using natural floor, subtraction, and Nat.clog; reason: d ≥ 3 and r ≥ 1 make clog exactly the stated ceiling; c ≥ 2t+1 excludes truncated-subtraction cases
--   - encoding: unordered distinct vertex pairs and a fixed reversal-consistent shortest-path system → sets of Sym2 V and PathSystem G, with paths only on reachable pairs; reason: each unordered pair is counted once and alignment uses the single fixed path
--   - generalization: each pair is charged to one selected realizing hop → a pair charges e whenever any realizing pivot pair has unordered hop e; reason: the geometric counting argument bounds all such pairs for a fixed hop and therefore every single-choice charging scheme
-- source:
--   Avi Kadria, Liam Roditty, STOC 2027 submission #584 (October 2026), Claim 1.3, p.19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/584.pdf

import Definitions.Def_PivotADO_OneHop_Charging

set_option autoImplicit false
open scoped Classical

namespace PivotADO.OneHop

/-- Claim 1.3, Kadria–Roditty, STOC 2027 submission #584 (October 2026), p.19.
The relation includes every realizing choice, hence every selected charging scheme. -/
theorem claim_1_3 {V : Type*} [Fintype V] (G : SimpleGraph V) (d g r : ℕ) (k : ℝ)
    (hd : G.IsRegularOfDegree d) (hg : G.egirth = (g : ℕ∞)) (hd3 : 3 ≤ d)
    (hr : 1 ≤ r) (hk : 1 ≤ k) (O : Oracle G r k) (P : PathSystem G)
    (hlarge : 2 * alignmentDepth d r + 1 ≤ pairDistance g k)
    (e : Sym2 V) (he : e ∈ O.storage.graph.edgeSet) :
    let c := pairDistance g k
    let t := alignmentDepth d r
    (Nat.card (chargedPairs O P c t e) : ℝ) ≤ 2 * (k * (c : ℝ) + 1) * ((d - 1 : ℕ) : ℝ) ^ (2 * t) := by sorry

end PivotADO.OneHop
