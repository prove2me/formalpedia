-- Prove2me | Theorems.Thm_TwoReLULayers_DepthCollapse_Supplement_cycle_boundary_iff_augmentation
-- name    : TwoReLULayers.DepthCollapse.Supplement.cycle_boundary_iff_augmentation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T22:28:36.415416+00:00
-- url     : https://prove2.me/theorems/008755b0-009a-4f94-9163-b6abba757b9f
-- title:
--   Lemma 11 — Boundary iff zero augmentation
-- statement:
--   Let $n,k\ge0$, choose arbitrary orientations of the simplex edges, and let $x\in C_k^n$ satisfy $d_Cx=0$. Then
--   $$\big(\exists y\in C_{k+1}^n:\ d_Cy=x\big)\quad\Longleftrightarrow\quad\varepsilon(x)=0.$$
--   Every chain and filling here is a finite rational linear combination of the actual formal cubical generators. This identifies the complete obstruction to filling a cycle, including degree zero of the ordinary, unaugmented complex.
--
--   Differences from the source:
--   - encoding: Rational polytopes in oriented subspaces, with Minkowski differences modulo translations and lower-dimensional terms → Finite rational vertex and ordered-frame presentation of the same geometric quotient; reason: The presentation imposes exactly those geometric relations; facet boundaries are evaluated on a chosen representative, with no extra hypothesis
--   - encoding: Group algebra tensored with the exterior power of the formally labeled simplex edges → Finite rational support on lattice points and increasing edge-label subsets; reason: This is its canonical basis presentation; dependent geometric edge vectors are not identified
--   - encoding: Simplex vertices labeled 1,…,n+1 → Simplex vertices labeled 0,…,n; reason: Only labels change; actual vertices, edges and facet cardinalities are the same
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026). Use this pinned PDF and its own labels; no arXiv version is asserted. p. 16, Lemma 11.

import Definitions.Def_TwoReLULayers_DepthCollapse_Supplement_Realization

namespace TwoReLULayers.DepthCollapse.Supplement

/-- Lemma 11, p.16, including degree zero of the ordinary complex. -/
theorem cycle_boundary_iff_augmentation (n k : ℕ) (o : EdgeOrientations n)
    (x : C n k) (hx : IsCycle o x) :
    IsBoundary o x ↔ epsilon x = 0 := by sorry

end TwoReLULayers.DepthCollapse.Supplement
