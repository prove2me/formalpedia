-- Prove2me | Theorems.Thm_TwoReLULayers_DepthCollapse_cover_refinement
-- name    : TwoReLULayers.DepthCollapse.cover_refinement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:35:05.82174+00:00
-- url     : https://prove2.me/theorems/ddd48c14-7fba-41a4-a562-5870ed0d96bf
-- title:
--   Geometric definition bridge — finite covers and polyhedral partitions
-- statement:
--   Let $n\ge1$, $R\subseteq\mathbb R$ be a subfield, and $f:E_n\to\mathbb R$. Then
--   $$f\in\operatorname{CPWL}(R,n)\quad\Longleftrightarrow\quad f\text{ is continuous and }R\text{-affine on every cell of a finite real hyperplane arrangement}.$$
--   The left side uses the independent finite closed polyhedral-cover definition. The right side uses all choices of closed sides of the arrangement hyperplanes, including empty cells. This establishes the geometric partition convention without restricting the cell normals to $R$.
--
--   Differences from the source:
--   - encoding: real inputs, field R containing the rationals, finite polyhedral partition and two hidden layers → Subfield ℝ, EuclideanSpace ℝ (Fin n), finite closed polyhedral cover and three affine-map evaluator; reason: every real subfield contains ℚ; common hyperplane refinement identifies the cover with a partition; widths remain arbitrary finite naturals
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026), p. 2, Section 1, geometric CPWL definition (unnumbered supporting bridge)

import Definitions.Def_TwoReLULayers_DepthCollapse_Construction

namespace TwoReLULayers.DepthCollapse

theorem cover_refinement {n : ℕ} (hn : 1 ≤ n) (R : Subfield ℝ) (f : E n → ℝ) :
    f ∈ CPWL R n ↔ ArrangementCPWL R n f := by sorry

end TwoReLULayers.DepthCollapse
