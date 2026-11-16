-- Prove2me | Theorems.Thm_TwoReLULayers_DepthCollapse_Supplement_simplex_boundary_lift
-- name    : TwoReLULayers.DepthCollapse.Supplement.simplex_boundary_lift
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T22:29:33.89613+00:00
-- url     : https://prove2.me/theorems/e37b54a3-3c07-49d7-ba8c-d28033a080af
-- title:
--   Lemma 13 — Lift the next simplex boundary
-- statement:
--   Let $n\ge2$, with arbitrary edge orientations in ambient dimensions $n$ and $n+1$. Suppose that some $x\in C_{n-1}^n$ satisfies
--   $$\rho(x)=[\Delta^n],\qquad\operatorname{FD}_n(d_Cx).$$
--   There is a chain $y\in C_{n-1}^{n+1}$ such that
--   $$d_Cy=0,\qquad\operatorname{FD}_{n+1}(y),\qquad
--   \rho(y)=d_P[\Delta^{n+1}].$$
--   The input face direction condition is on the boundary of $x$. In the output the degree remains $n-1$, but the ambient dimension and the cardinality of a witnessing simplex facet increase by one. This is the boundary-lifting statement used in the simplex construction.
--
--   Differences from the source:
--   - encoding: Rational polytopes in oriented subspaces, with Minkowski differences modulo translations and lower-dimensional terms → Finite rational vertex and ordered-frame presentation of the same geometric quotient; reason: The presentation imposes exactly those geometric relations; facet boundaries are evaluated on a chosen representative, with no extra hypothesis
--   - encoding: Group algebra tensored with the exterior power of the formally labeled simplex edges → Finite rational support on lattice points and increasing edge-label subsets; reason: This is its canonical basis presentation; dependent geometric edge vectors are not identified
--   - encoding: n ≥ 2 → n = m+2, m : ℕ; reason: Equivalent enumeration of every permitted natural dimension or degree; avoids dependent transports from natural subtraction
--   - encoding: Simplex vertices labeled 1,…,n+1 → Simplex vertices labeled 0,…,n; reason: Only labels change; actual vertices, edges and facet cardinalities are the same
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026). Use this pinned PDF and its own labels; no arXiv version is asserted. p. 18, Lemma 13.

import Definitions.Def_TwoReLULayers_DepthCollapse_Supplement_Realization

namespace TwoReLULayers.DepthCollapse.Supplement

/-- Lemma 13, p.18. Ambient n+2 ranges over every n of the source with n≥2.
The input condition is imposed on d(x), not on x. -/
theorem simplex_boundary_lift (n : ℕ)
    (o : EdgeOrientations (n + 2)) (o' : EdgeOrientations (n + 3))
    (h : ∃ x : C (n + 2) (n + 1), rho o x = simplexClass (n + 2) ∧
      FaceDirection o (dC o x)) :
    ∃ y : C (n + 3) (n + 1), IsCycle o' y ∧ FaceDirection o' y ∧
      rho o' y = dP (n + 3) (n + 3) (simplexClass (n + 3)) := by sorry

end TwoReLULayers.DepthCollapse.Supplement
