-- Prove2me | Theorems.Thm_SierpinskiSeparates_separates
-- name    : SierpinskiSeparates.separates
-- status  : Open
-- author  : @LG
-- created : 2026-11-26T20:35:11.006537+00:00
-- url     : https://prove2.me/theorems/03308492-fd51-4742-b324-d099a12232f4
-- title:
--   The Sierpinski tetrahedron separates knot types
-- statement:
--   **The Sierpinski tetrahedron separates knot types.** There exist tame knots $K_1$ and $K_2$ such that $K_1$ embeds in the $1$-skeleton of some finite iteration of the Sierpinski tetrahedron, while $K_2$ embeds in none:
--   $$\exists K_1\,K_2,\ \bigl(\exists n,\ \mathrm{EmbedsInSierpinski}\ K_1\ n\bigr)\ \wedge\ \bigl(\forall n,\ \neg\,\mathrm{EmbedsInSierpinski}\ K_2\ n\bigr).$$
--   This answers the final question of *Knots Inside Fractals* (arXiv:2409.03639, §6) in the affirmative: the Sierpinski tetrahedron is a fractal, produced by an iterative process, that admits certain knot types but not others. It is proved by combining Espinosa's non-embedding theorem (arXiv:2609.24545, Theorem A) with the embeddability of, e.g., the unknot. It also disproves Conjecture 1 of *Knots Inside Fractals*.
-- source:
--   Espinosa, Knots and the Sierpinski Tetrahedron, https://arxiv.org/abs/2609.24545, Theorem A; resolving Broden–Espinosa–Nazareth–Voth, Knots Inside Fractals, https://arxiv.org/abs/2409.03639, §6 Final Question

import Mathlib
import Definitions.Def_KnotsInsideFractals_fractals
import Definitions.Def_KnotsInsideFractals_knots
open Set KnotsInsideFractals

namespace SierpinskiSeparates
theorem separates : ∃ K₁ K₂ : PolygonalKnot, (∃ n, EmbedsInSierpinski K₁ n) ∧ (∀ n, ¬ EmbedsInSierpinski K₂ n) := by sorry
end SierpinskiSeparates
