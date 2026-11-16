-- Prove2me | Theorems.Thm_TwoReLULayers_DepthCollapse_Supplement_top_differential_injective
-- name    : TwoReLULayers.DepthCollapse.Supplement.top_differential_injective
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T22:26:42.411478+00:00
-- url     : https://prove2.me/theorems/b24071d3-db32-4d7f-b332-f042796dea1c
-- title:
--   Lemma 3 — Top boundary injectivity
-- statement:
--   Let $n\ge2$. In the rational oriented polytope quotient $P_\bullet^n$, the top boundary is injective:
--   $$d_P:P_n^n\longrightarrow P_{n-1}^n\quad\text{is injective}.$$
--   The assertion applies to every class in the geometric quotient, including classes not known to lie in the paramid span. It identifies a top-dimensional class by its boundary.
--
--   Differences from the source:
--   - encoding: Rational polytopes in oriented subspaces, with Minkowski differences modulo translations and lower-dimensional terms → Finite rational vertex and ordered-frame presentation of the same geometric quotient; reason: The presentation imposes exactly those geometric relations; facet boundaries are evaluated on a chosen representative, with no extra hypothesis
--   - encoding: n ≥ 2 → n = m+2, m : ℕ; reason: Equivalent enumeration of every permitted natural dimension or degree; avoids dependent transports from natural subtraction
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026). Use this pinned PDF and its own labels; no arXiv version is asserted. p. 11, Lemma 3.

import Definitions.Def_TwoReLULayers_DepthCollapse_Supplement_Realization

namespace TwoReLULayers.DepthCollapse.Supplement

/-- Lemma 3, p.11. The parameter n+2 ranges over every ambient dimension ≥2. -/
theorem top_differential_injective (n : ℕ) :
    Function.Injective (dP (n + 2) (n + 2)) := by sorry

end TwoReLULayers.DepthCollapse.Supplement
