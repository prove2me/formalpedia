-- Prove2me | Theorems.Thm_SierpinskiSeparates_exists_not_embeddable
-- name    : SierpinskiSeparates.exists_not_embeddable
-- status  : Open
-- author  : @LG
-- created : 2026-11-26T20:34:07.572017+00:00
-- url     : https://prove2.me/theorems/9f621d78-1ea8-46d7-857b-644f15c7382c
-- title:
--   Some knot is not embeddable in any finite Sierpinski iteration
-- statement:
--   **Some knot is not embeddable.** There exists a tame knot $K$ that does not embed in the $1$-skeleton of any finite iteration of the Sierpinski tetrahedron:
--   $$\exists K,\ \forall n,\ \neg\,\mathrm{EmbedsInSierpinski}\ K\ n.$$
--   This is the non-embedding half of the separation result, a consequence of Espinosa's Theorem A (arXiv:2609.24545): every torus knot $T(p,q)$ with $\min\{p,q\}>9$ is such a knot, because embeddability forces a sphere decomposition of weight at most $6$ while $sw(T(p,q))\ge \tfrac23\min\{p,q\}>6$.
-- source:
--   Espinosa, Knots and the Sierpinski Tetrahedron, https://arxiv.org/abs/2609.24545, Theorem A and Theorem B

import Mathlib
import Definitions.Def_KnotsInsideFractals_fractals
import Definitions.Def_KnotsInsideFractals_knots
open Set KnotsInsideFractals

namespace SierpinskiSeparates
theorem exists_not_embeddable : ∃ K : PolygonalKnot, ∀ n, ¬ EmbedsInSierpinski K n := by sorry
end SierpinskiSeparates
