-- Prove2me | Theorems.Thm_PivotADO_OneHop_counting_inequality
-- name    : PivotADO.OneHop.counting_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:15:43.219202+00:00
-- url     : https://prove2.me/theorems/f81245cd-7eb9-4d8c-8934-5cf4ee37069f
-- title:
--   §5.1 — the exact graph-level counting inequality
-- statement:
--   Let $G$ be a finite $d$-regular graph of finite girth $g$, with $n=|V|$, $d\ge3$, integer $r\ge1$, and real $k\ge1$. Fix any $r$-pivot 1-hop $k$-stretch oracle $(H,\mathcal P)$ and any fixed reversal-consistent shortest-path system $P$. Set $c=\lfloor g/(k+1)\rfloor-1$ and $t=1+\lceil\log_{d-1}(4r)\rceil$, and assume the source's standing large-distance condition $c\ge2t+1$.
--
--   Writing $E_H$ for the unordered stored edges, one has
--
--   $$2(kc+1)(d-1)^{2t}|E_H|\ge\frac14 n d(d-1)^{c-1}.$$
--
--   This is the full graph-level estimate with its displayed constants. It is unconditional: Conjecture 1 is not a hypothesis. Its role is to convert local structure into a space lower bound on any graph satisfying the stated setting, before choosing a conjectural graph family.
--
--   Differences from the source:
--   - encoding: a finite vertex set V → an arbitrary Fintype V with classical equality and adjacency decisions; reason: finite relabeling and decidability choices change no graph
--   - encoding: finite girth g and shortest-path distance, infinite between components → G.egirth = (g : ℕ∞) and G.edist; weighted distances use ENat.toENNReal; reason: acyclic and disconnected inputs retain their infinite values
--   - generalization: finite nonnegative edge weights → edge weights in ℝ≥0∞, including infinity; reason: an infinite-weight stored edge is counted and cannot improve any finite query; finite-weight oracles are included
--   - encoding: c = floor(g/(k+1))-1 and t = 1+ceil(log base d-1 of 4r) → pairDistance g k and alignmentDepth d r using natural floor, subtraction, and Nat.clog; reason: d ≥ 3 and r ≥ 1 make clog exactly the stated ceiling; c ≥ 2t+1 excludes truncated-subtraction cases
--   - encoding: unordered distinct vertex pairs and a fixed reversal-consistent shortest-path system → sets of Sym2 V and PathSystem G, with paths only on reachable pairs; reason: each unordered pair is counted once and alignment uses the single fixed path
-- source:
--   Avi Kadria, Liam Roditty, STOC 2027 submission #584 (October 2026), §5.1 counting inequality, p.20; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/584.pdf

import Definitions.Def_PivotADO_OneHop_Charging

set_option autoImplicit false
open scoped Classical

namespace PivotADO.OneHop

/-- §5.1 counting inequality, Kadria–Roditty, STOC 2027 submission #584
(October 2026), p.20. This graph-level statement does not assume Conjecture 1. -/
theorem counting_inequality {V : Type*} [Fintype V] (G : SimpleGraph V) (d g r : ℕ) (k : ℝ)
    (hd : G.IsRegularOfDegree d) (hg : G.egirth = (g : ℕ∞)) (hd3 : 3 ≤ d)
    (hr : 1 ≤ r) (hk : 1 ≤ k) (O : Oracle G r k) (P : PathSystem G)
    (hlarge : 2 * alignmentDepth d r + 1 ≤ pairDistance g k) :
    let c := pairDistance g k
    let t := alignmentDepth d r
    (1 / 4 : ℝ) * (Fintype.card V : ℝ) * (d : ℝ) * ((d - 1 : ℕ) : ℝ) ^ (c - 1) ≤
      2 * (k * (c : ℝ) + 1) * ((d - 1 : ℕ) : ℝ) ^ (2 * t) * (edgeCount O.storage.graph : ℝ) := by sorry

end PivotADO.OneHop
