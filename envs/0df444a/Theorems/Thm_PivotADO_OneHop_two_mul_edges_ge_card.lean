-- Prove2me | Theorems.Thm_PivotADO_OneHop_two_mul_edges_ge_card
-- name    : PivotADO.OneHop.two_mul_edges_ge_card
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:14:04.296793+00:00
-- url     : https://prove2.me/theorems/5392d0eb-b98e-4924-844c-dfaeb02ed2e5
-- title:
--   §5.1 — every vertex meets a stored edge
-- statement:
--   Let $G$ be a finite $d$-regular graph with $d\ge1$, and let $(H,\mathcal P)$ be an $r$-pivot 1-hop $k$-stretch oracle, where $r\ge1$ and $k\ge1$. Then
--
--   $$|V|\le2|E_H|.$$
--
--   This is the source's linear space bound, used when the prescribed distance $c$ is smaller than $2t+1$. It does not require a finite girth or the large-$c$ condition. It formalizes the last clause of the cited passage; the asymptotic small-$c$ arithmetic remains in the full goal.
--
--   Differences from the source:
--   - encoding: a finite vertex set V → an arbitrary Fintype V with classical equality and adjacency decisions; reason: finite relabeling and decidability choices change no graph
--   - generalization: finite nonnegative edge weights → edge weights in ℝ≥0∞, including infinity; reason: an infinite-weight stored edge is counted and cannot improve any finite query; finite-weight oracles are included
--   - generalization: the §5.1 high-girth d-regular graph with d ≥ 3 → every finite d-regular graph with d ≥ 1, without a girth hypothesis; reason: the stated incidence argument only needs that every vertex has a neighbor
-- source:
--   Avi Kadria, Liam Roditty, STOC 2027 submission #584 (October 2026), §5.1, every vertex must be incident to an edge of H, p.18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/584.pdf

import Definitions.Def_PivotADO_OneHop_Oracle

set_option autoImplicit false
open scoped Classical

namespace PivotADO.OneHop

/-- §5.1, Kadria–Roditty, STOC 2027 submission #584 (October 2026), p.18:
every vertex meets a stored edge, even in the small-c case. -/
theorem two_mul_edges_ge_card {V : Type*} [Fintype V] (G : SimpleGraph V)
    (d r : ℕ) (k : ℝ) (hd : G.IsRegularOfDegree d) (hdpos : 1 ≤ d)
    (hr : 1 ≤ r) (hk : 1 ≤ k) (O : Oracle G r k) :
    Fintype.card V ≤ 2 * edgeCount O.storage.graph := by sorry

end PivotADO.OneHop
