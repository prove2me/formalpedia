-- Prove2me | Theorems.Thm_TwoReLULayers_DepthCollapse_rational_field_extension
-- name    : TwoReLULayers.DepthCollapse.rational_field_extension
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:35:45.531507+00:00
-- url     : https://prove2.me/theorems/46d39526-e258-4ce2-b64e-cdf628aacef6
-- title:
--   Rational network coefficients embed into any real subfield
-- statement:
--   Let $n\ge1$ and let $R$ be any subfield of $\mathbb R$. Every rational-coefficient two-hidden-layer network is also a network over $R$:
--   $$\operatorname{ReLU2}(\mathbb Q,n)\subseteq\operatorname{ReLU2}(R,n).$$
--   Inputs and outputs stay real and the computed function is unchanged. This makes explicit the field inclusion used to pass from rational MAX networks to the full goal.
--
--   Differences from the source:
--   - encoding: finite Euclidean coordinates and finite index families → EuclideanSpace ℝ (Fin n), Fin k and pointwise function identities; reason: canonical coordinate identification and reindexing preserve every source instance
--   - encoding: the field ℚ inside ℝ → the bottom real subfield; reason: the prime subfield of ℝ consists exactly of rational numbers
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026), p. 3, Section 1, reduction to rational MAX after Theorem 1

import Definitions.Def_TwoReLULayers_DepthCollapse_Construction

namespace TwoReLULayers.DepthCollapse

theorem rational_field_extension {n : ℕ} (hn : 1 ≤ n) (R : Subfield ℝ)
    (f : E n → ℝ) (hf : f ∈ ReLU2 (⊥ : Subfield ℝ) n) :
    f ∈ ReLU2 R n := by sorry

end TwoReLULayers.DepthCollapse
