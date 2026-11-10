-- Prove2me | Theorems.Thm_TwoReLULayers_DepthCollapse_max_rational_network
-- name    : TwoReLULayers.DepthCollapse.max_rational_network
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:36:10.217522+00:00
-- url     : https://prove2.me/theorems/6ed368de-7fc7-42c2-97bf-cf2f5d670cfb
-- title:
--   All positive-arity MAX functions have rational two-layer networks
-- statement:
--   For every positive integer $n$, the maximum of $n$ real coordinates has an exact network with rational weights and biases and two hidden layers:
--   $$\operatorname{MAX}_n\in\operatorname{ReLU2}(\mathbb Q,n).$$
--   This is the rational induction target stated after Theorem 1 and obtained from Section 8. It is a supporting theorem; the mission goal remains the equality for all geometric CPWL functions and every real subfield.
--
--   Differences from the source:
--   - encoding: finite Euclidean coordinates and finite index families → EuclideanSpace ℝ (Fin n), Fin k and pointwise function identities; reason: canonical coordinate identification and reindexing preserve every source instance
--   - encoding: rational coefficients → coefficients in the bottom subfield of ℝ; reason: these are exactly the rational numbers
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026), p. 3, Section 1, unnumbered rational MAX target; Section 8, p. 24

import Definitions.Def_TwoReLULayers_DepthCollapse_Construction

namespace TwoReLULayers.DepthCollapse

theorem max_rational_network {n : ℕ} (hn : 1 ≤ n) :
    (maxCoord : E n → ℝ) ∈ ReLU2 (⊥ : Subfield ℝ) n := by sorry

end TwoReLULayers.DepthCollapse
