-- Prove2me | Theorems.Thm_TwoReLULayers_DepthCollapse_Supplement_realization_boundary
-- name    : TwoReLULayers.DepthCollapse.Supplement.realization_boundary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T22:27:32.690446+00:00
-- url     : https://prove2.me/theorems/608d0cd0-1ce3-42ae-a7e1-d88ef61607ac
-- title:
--   Lemma 10 — Coning commutes with boundary
-- statement:
--   Let $n\ge0$, fix arbitrary orientations of all edges of the standard $n$-simplex, and let $k\ge2$. For every formal cubical chain $x\in C_k^n$,
--   $$d_P\rho(x)=\rho(d_Cx).$$
--   The quantifier includes geometrically degenerate formal generators. This gives the compatibility between the cubical boundary and the geometric paramid realization in precisely the degrees used by the construction.
--
--   Differences from the source:
--   - encoding: Rational polytopes in oriented subspaces, with Minkowski differences modulo translations and lower-dimensional terms → Finite rational vertex and ordered-frame presentation of the same geometric quotient; reason: The presentation imposes exactly those geometric relations; facet boundaries are evaluated on a chosen representative, with no extra hypothesis
--   - encoding: Group algebra tensored with the exterior power of the formally labeled simplex edges → Finite rational support on lattice points and increasing edge-label subsets; reason: This is its canonical basis presentation; dependent geometric edge vectors are not identified
--   - encoding: k ≥ 2 → k = m+2, m : ℕ; reason: Equivalent enumeration of every permitted natural dimension or degree; avoids dependent transports from natural subtraction
--   - encoding: Simplex vertices labeled 1,…,n+1 → Simplex vertices labeled 0,…,n; reason: Only labels change; actual vertices, edges and facet cardinalities are the same
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026). Use this pinned PDF and its own labels; no arXiv version is asserted. p. 15, Lemma 10.

import Definitions.Def_TwoReLULayers_DepthCollapse_Supplement_Realization

namespace TwoReLULayers.DepthCollapse.Supplement

/-- Lemma 10, p.15. Degree k+2 ranges over every degree ≥2. -/
theorem realization_boundary (n k : ℕ) (o : EdgeOrientations n) (x : C n (k + 2)) :
    dP n (k + 3) (rho o x) = rho o (dC o x) := by sorry

end TwoReLULayers.DepthCollapse.Supplement
