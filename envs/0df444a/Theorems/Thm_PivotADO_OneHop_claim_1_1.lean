-- Prove2me | Theorems.Thm_PivotADO_OneHop_claim_1_1
-- name    : PivotADO.OneHop.claim_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:15:24.373143+00:00
-- url     : https://prove2.me/theorems/4bd5d144-ce7a-4e22-9e0a-883e6189467b
-- title:
--   Claim 1.1 — at least one quarter of the regular sphere count
-- statement:
--   Let $G$ be a finite $d$-regular graph of finite girth $g$, with $n=|V|$, $d\ge3$, integer $r\ge1$, and real $k\ge1$. Fix any $r$-pivot 1-hop $k$-stretch oracle $(H,\mathcal P)$ and any fixed reversal-consistent shortest-path system $P$. Set $c=\lfloor g/(k+1)\rfloor-1$ and $t=1+\lceil\log_{d-1}(4r)\rceil$, and assume the source's standing large-distance condition $c\ge2t+1$.
--
--   Let $\mathcal N$ be the set of non-aligned unordered pairs at distance $c$. Then
--
--   $$4|\mathcal N|\ge n d(d-1)^{c-1}.$$
--
--   The count uses unordered distinct pairs and retains the exact constant $1/4$. This supplies the population of queries to be charged to stored hops.
--
--   Differences from the source:
--   - encoding: a finite vertex set V → an arbitrary Fintype V with classical equality and adjacency decisions; reason: finite relabeling and decidability choices change no graph
--   - encoding: finite girth g and shortest-path distance, infinite between components → G.egirth = (g : ℕ∞) and G.edist; weighted distances use ENat.toENNReal; reason: acyclic and disconnected inputs retain their infinite values
--   - generalization: finite nonnegative edge weights → edge weights in ℝ≥0∞, including infinity; reason: an infinite-weight stored edge is counted and cannot improve any finite query; finite-weight oracles are included
--   - encoding: c = floor(g/(k+1))-1 and t = 1+ceil(log base d-1 of 4r) → pairDistance g k and alignmentDepth d r using natural floor, subtraction, and Nat.clog; reason: d ≥ 3 and r ≥ 1 make clog exactly the stated ceiling; c ≥ 2t+1 excludes truncated-subtraction cases
--   - encoding: unordered distinct vertex pairs and a fixed reversal-consistent shortest-path system → sets of Sym2 V and PathSystem G, with paths only on reachable pairs; reason: each unordered pair is counted once and alignment uses the single fixed path
--   - encoding: at least (1/4) n d(d-1)^(c-1) pairs → n d(d-1)^(c-1) ≤ 4 times the natural cardinality; reason: multiplication by four preserves exactly the stated constant
-- source:
--   Avi Kadria, Liam Roditty, STOC 2027 submission #584 (October 2026), Claim 1.1, p.18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/584.pdf

import Definitions.Def_PivotADO_OneHop_Charging

set_option autoImplicit false
open scoped Classical

namespace PivotADO.OneHop

/-- Claim 1.1, Kadria–Roditty, STOC 2027 submission #584 (October 2026), p.18. -/
theorem claim_1_1 {V : Type*} [Fintype V] (G : SimpleGraph V) (d g r : ℕ) (k : ℝ)
    (hd : G.IsRegularOfDegree d) (hg : G.egirth = (g : ℕ∞)) (hd3 : 3 ≤ d)
    (hr : 1 ≤ r) (hk : 1 ≤ k) (O : Oracle G r k) (P : PathSystem G)
    (hlarge : 2 * alignmentDepth d r + 1 ≤ pairDistance g k) :
    let c := pairDistance g k
    let t := alignmentDepth d r
    Fintype.card V * d * (d - 1) ^ (c - 1) ≤ 4 * Nat.card (nonAlignedPairs O P c t) := by sorry

end PivotADO.OneHop
