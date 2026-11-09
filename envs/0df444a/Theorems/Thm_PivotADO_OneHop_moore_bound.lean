-- Prove2me | Theorems.Thm_PivotADO_OneHop_moore_bound
-- name    : PivotADO.OneHop.moore_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:29.90134+00:00
-- url     : https://prove2.me/theorems/f5cba52b-5274-420e-ba39-631be63050fb
-- title:
--   §2.1 — Moore bound and uniform logarithmic girth bound
-- statement:
--   Let $G$ be a finite $d$-regular graph of finite girth $g$, with $n$ vertices. For every integer $\ell\ge0$ with $g\ge2\ell+1$,
--
--   $$n\ge(d-1)^\ell.$$
--
--   In the same statement, if $d\ge3$, then
--
--   $$g\le2\log_{d-1}n+2.$$
--
--   The additive constant $2$ is uniform over $d,G,n$ and makes the source's $O(1)$ explicit. This provides the girth upper bound used by the graph-level counting estimate. Finite girth excludes empty and acyclic graphs.
--
--   Differences from the source:
--   - encoding: a finite vertex set V → an arbitrary Fintype V with classical equality and adjacency decisions; reason: finite relabeling and decidability choices change no graph
--   - encoding: finite girth g and shortest-path distance, infinite between components → G.egirth = (g : ℕ∞) and G.edist; weighted distances use ENat.toENNReal; reason: acyclic and disconnected inputs retain their infinite values
--   - generalization: g ≤ 2 log base d-1 of n + O(1) for constant d → g ≤ 2 log base d-1 of n + 2 uniformly for every d ≥ 3; reason: taking ℓ = floor((g-1)/2) in the first clause gives g ≤ 2ℓ+2 and ℓ ≤ log base d-1 of n
-- source:
--   Avi Kadria, Liam Roditty, STOC 2027 submission #584 (October 2026), §2.1 Moore bound, p.6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/584.pdf

import Definitions.Def_PivotADO_OneHop_Geometry

set_option autoImplicit false
open scoped Classical

namespace PivotADO.OneHop

/-- §2.1 Moore bound, Kadria–Roditty, STOC 2027 submission #584 (October 2026), p.6.
The uniform additive constant 2 makes the printed O(1) explicit. -/
theorem moore_bound {V : Type*} [Fintype V] (G : SimpleGraph V) (d g : ℕ)
    (hd : G.IsRegularOfDegree d) (hg : G.egirth = (g : ℕ∞)) :
    (∀ ℓ : ℕ, 2 * ℓ + 1 ≤ g → (d - 1) ^ ℓ ≤ Fintype.card V) ∧
    (3 ≤ d → (g : ℝ) ≤ 2 * Real.logb ((d : ℝ) - 1) (Fintype.card V : ℝ) + 2) := by sorry

end PivotADO.OneHop
