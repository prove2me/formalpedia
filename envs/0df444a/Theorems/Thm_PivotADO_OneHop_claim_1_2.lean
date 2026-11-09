-- Prove2me | Theorems.Thm_PivotADO_OneHop_claim_1_2
-- name    : PivotADO.OneHop.claim_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:14:59.067143+00:00
-- url     : https://prove2.me/theorems/015ab5f9-5ef2-48bf-8b93-9fae1e59384b
-- title:
--   Claim 1.2 — the middle segment lies on the realizing hop path
-- statement:
--   Let $G$ be a finite $d$-regular graph of finite girth $g$, with $n=|V|$, $d\ge3$, integer $r\ge1$, and real $k\ge1$. Fix any $r$-pivot 1-hop $k$-stretch oracle $(H,\mathcal P)$ and any fixed reversal-consistent shortest-path system $P$. Set $c=\lfloor g/(k+1)\rfloor-1$ and $t=1+\lceil\log_{d-1}(4r)\rceil$, and assume the source's standing large-distance condition $c\ge2t+1$.
--
--   Let $\{u,v\}$ be non-aligned, and choose pivots $p_u\in\mathcal P(u)$, $p_v\in\mathcal P(v)$ realizing the estimate minimum. On $P(u,v)$, let $q_u$ be $t$ edges from $u$ and $q_v$ be $t$ edges from $v$, and let $Q$ be the intervening edge segment. Then
--
--   $$\varnothing\ne E(Q)\subseteq E(P(p_u,p_v)),\qquad \{p_u,p_v\}\in E_H.$$
--
--   The theorem supplies reachability of both endpoint pairs as well as the inclusion. Its segment is constructed from the fixed path by dropping $t$ edges and taking $c-2t$ edges. The nonemptiness and actual stored-hop conclusions are the immediate consequences recorded in the same source passage. No acyclicity of the union of paths or bound (5.4) is assumed.
--
--   Differences from the source:
--   - encoding: a finite vertex set V → an arbitrary Fintype V with classical equality and adjacency decisions; reason: finite relabeling and decidability choices change no graph
--   - encoding: finite girth g and shortest-path distance, infinite between components → G.egirth = (g : ℕ∞) and G.edist; weighted distances use ENat.toENNReal; reason: acyclic and disconnected inputs retain their infinite values
--   - generalization: finite nonnegative edge weights → edge weights in ℝ≥0∞, including infinity; reason: an infinite-weight stored edge is counted and cannot improve any finite query; finite-weight oracles are included
--   - encoding: c = floor(g/(k+1))-1 and t = 1+ceil(log base d-1 of 4r) → pairDistance g k and alignmentDepth d r using natural floor, subtraction, and Nat.clog; reason: d ≥ 3 and r ≥ 1 make clog exactly the stated ceiling; c ≥ 2t+1 excludes truncated-subtraction cases
--   - encoding: unordered distinct vertex pairs and a fixed reversal-consistent shortest-path system → sets of Sym2 V and PathSystem G, with paths only on reachable pairs; reason: each unordered pair is counted once and alignment uses the single fixed path
--   - encoding: Q = P(q_u,q_v), the subpath of P(u,v), of length c-2t ≥ 1 → middleEdges, formed by dropping t and taking c-2t edges, with explicit nonemptiness and adjacency; reason: this constructs precisely the source segment; local uniqueness identifies it with P(q_u,q_v), and a finite realizing cost with distinct pivots forces a stored edge
-- source:
--   Avi Kadria, Liam Roditty, STOC 2027 submission #584 (October 2026), Claim 1.2 and its surrounding construction, p.19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/584.pdf

import Definitions.Def_PivotADO_OneHop_Charging

set_option autoImplicit false
open scoped Classical

namespace PivotADO.OneHop

/-- Claim 1.2 and its actual-hop consequence, Kadria–Roditty,
STOC 2027 submission #584 (October 2026), p.19. Q is the constructed middle segment.
No acyclicity or distance-sum bound from the proof is assumed. -/
theorem claim_1_2 {V : Type*} [Fintype V] (G : SimpleGraph V) (d g r : ℕ) (k : ℝ)
    (hd : G.IsRegularOfDegree d) (hg : G.egirth = (g : ℕ∞)) (hd3 : 3 ≤ d)
    (hr : 1 ≤ r) (hk : 1 ≤ k) (O : Oracle G r k) (P : PathSystem G)
    (hlarge : 2 * alignmentDepth d r + 1 ≤ pairDistance g k)
    (u v pu pv : V) (hna : NonAligned O P (pairDistance g k) (alignmentDepth d r) u v)
    (hrealizes : Realizes O u v pu pv) :
    ∃ (huv : G.Reachable u v) (hpp : G.Reachable pu pv),
      O.storage.graph.Adj pu pv ∧
      middleEdges P (pairDistance g k) (alignmentDepth d r) u v huv ≠ [] ∧
      ∀ e ∈ middleEdges P (pairDistance g k) (alignmentDepth d r) u v huv,
        e ∈ (P.path pu pv hpp).edges := by sorry

end PivotADO.OneHop
