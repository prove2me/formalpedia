-- Prove2me | Theorems.Thm_TwoReLULayers_DepthCollapse_cpwl_eq_relu_two
-- name    : TwoReLULayers.DepthCollapse.cpwl_eq_relu_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:35:56.52104+00:00
-- url     : https://prove2.me/theorems/f957fc50-db3b-423c-ad41-ff8310c31ecb
-- title:
--   Theorem 1 — exact two-hidden-layer representation of CPWL functions
-- statement:
--   For every integer $n\ge1$ and every subfield $R\subseteq\mathbb R$ containing the rational numbers,
--   $$\operatorname{CPWL}_n(R)=\operatorname{ReLU}_{n,2}(R).$$
--   The left side consists of globally continuous real-valued functions on all of $\mathbb R^n$ with a finite geometric polyhedral partition and affine pieces whose coefficients lie in $R$. The right side consists of outputs of actual finite-width networks with two hidden layers, three affine maps, weights and biases in $R$, entrywise ReLU between the affine maps, and no output activation. Equality includes both directions and is pointwise on the entire real input space. There is no approximation error, width bound, homogeneity assumption or restriction to rational inputs.
--
--   **Formalization Note** The finite-cover presentation of geometric CPWL is identified with a partition by the separate arrangement-refinement bridge. Width zero is harmless; all widths remain existential and finite.
--
--   Differences from the source:
--   - encoding: real inputs, field R containing the rationals, finite polyhedral partition and two hidden layers → Subfield ℝ, EuclideanSpace ℝ (Fin n), finite closed polyhedral cover and three affine-map evaluator; reason: every real subfield contains ℚ; common hyperplane refinement identifies the cover with a partition; widths remain arbitrary finite naturals
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026), p. 3, Theorem 1

import Definitions.Def_TwoReLULayers_DepthCollapse_Construction

namespace TwoReLULayers.DepthCollapse

theorem cpwl_eq_relu_two {n : ℕ} (hn : 1 ≤ n) (R : Subfield ℝ) :
    CPWL R n = ReLU2 R n := by sorry

end TwoReLULayers.DepthCollapse
