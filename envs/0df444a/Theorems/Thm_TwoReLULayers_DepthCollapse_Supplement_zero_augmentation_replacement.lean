-- Prove2me | Theorems.Thm_TwoReLULayers_DepthCollapse_Supplement_zero_augmentation_replacement
-- name    : TwoReLULayers.DepthCollapse.Supplement.zero_augmentation_replacement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T22:29:10.073332+00:00
-- url     : https://prove2.me/theorems/2d8e429c-e8d5-41cf-a061-e7ff1078e880
-- title:
--   Lemma 12 — Cycle replacement with zero augmentation
-- statement:
--   Let $n\ge0$, choose arbitrary orientations of the simplex edges, and let $x\in C_k^n$ be a cycle with $k\ge2$. There is a chain $x'\in C_k^n$ satisfying all of
--   $$d_Cx'=0,\qquad\varepsilon(x')=0,\qquad\rho(x')=\rho(x),\qquad
--   \big(\operatorname{FD}(x)\Rightarrow\operatorname{FD}(x')\big).$$
--   Here $\operatorname{FD}$ denotes the face direction condition, with a separate facet direction witness for each nonzero basis term. The preservation condition concerns the same chosen $x'$ and is conditional; it imposes no face direction assumption on the input. This permits the zero-augmentation requirement to be met while retaining the geometric realization.
--
--   Differences from the source:
--   - encoding: Rational polytopes in oriented subspaces, with Minkowski differences modulo translations and lower-dimensional terms → Finite rational vertex and ordered-frame presentation of the same geometric quotient; reason: The presentation imposes exactly those geometric relations; facet boundaries are evaluated on a chosen representative, with no extra hypothesis
--   - encoding: Group algebra tensored with the exterior power of the formally labeled simplex edges → Finite rational support on lattice points and increasing edge-label subsets; reason: This is its canonical basis presentation; dependent geometric edge vectors are not identified
--   - encoding: k ≥ 2 → k = m+2, m : ℕ; reason: Equivalent enumeration of every permitted natural dimension or degree; avoids dependent transports from natural subtraction
--   - encoding: Simplex vertices labeled 1,…,n+1 → Simplex vertices labeled 0,…,n; reason: Only labels change; actual vertices, edges and facet cardinalities are the same
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026). Use this pinned PDF and its own labels; no arXiv version is asserted. p. 18, Lemma 12.

import Definitions.Def_TwoReLULayers_DepthCollapse_Supplement_Realization

namespace TwoReLULayers.DepthCollapse.Supplement

/-- Lemma 12, p.18; the same witness preserves face directions conditionally. -/
theorem zero_augmentation_replacement (n k : ℕ) (o : EdgeOrientations n)
    (x : C n (k + 2)) (hx : IsCycle o x) :
    ∃ x' : C n (k + 2), IsCycle o x' ∧ epsilon x' = 0 ∧ rho o x' = rho o x ∧
      (FaceDirection o x → FaceDirection o x') := by sorry

end TwoReLULayers.DepthCollapse.Supplement
