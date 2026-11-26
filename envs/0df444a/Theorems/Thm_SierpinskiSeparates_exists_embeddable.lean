-- Prove2me | Theorems.Thm_SierpinskiSeparates_exists_embeddable
-- name    : SierpinskiSeparates.exists_embeddable
-- status  : Open
-- author  : @LG
-- created : 2026-11-26T20:34:33.68334+00:00
-- url     : https://prove2.me/theorems/60d4994f-e98d-452b-b5db-4c0379c6a968
-- title:
--   Some knot is embeddable in a finite Sierpinski iteration
-- statement:
--   **Some knot is embeddable.** There exists a tame knot $K$ and a finite iteration of the Sierpinski tetrahedron whose $1$-skeleton contains an ambient-isotopic copy of $K$:
--   $$\exists K,\ \exists n,\ \mathrm{EmbedsInSierpinski}\ K\ n.$$
--   This is the embeddable half of the separation result. It is elementary — the unknot already lies on a triangular face of the first iteration — and is also implied by *Knots Inside Fractals* (arXiv:2409.03639, Theorem 2), which embeds every pretzel knot.
-- source:
--   Broden–Espinosa–Nazareth–Voth, Knots Inside Fractals, https://arxiv.org/abs/2409.03639, Theorem 2; cf. Espinosa, https://arxiv.org/abs/2609.24545

import Mathlib
import Definitions.Def_KnotsInsideFractals_fractals
import Definitions.Def_KnotsInsideFractals_knots
open Set KnotsInsideFractals

namespace SierpinskiSeparates
theorem exists_embeddable : ∃ K : PolygonalKnot, ∃ n, EmbedsInSierpinski K n := by sorry
end SierpinskiSeparates
