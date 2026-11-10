-- Prove2me | Theorems.Thm_TwoReLULayers_DepthCollapse_network_geometric_cpwl
-- name    : TwoReLULayers.DepthCollapse.network_geometric_cpwl
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:35:56.497204+00:00
-- url     : https://prove2.me/theorems/b5066696-11b9-44ea-bffd-5c57ce226062
-- title:
--   Reverse inclusion — activation partitions are geometric CPWL
-- statement:
--   For every positive input dimension $n$, every real subfield $R$, and every actual two-hidden-layer network $N$ over $R$,
--   $$N\text{'s output}\in\operatorname{CPWL}(R,n).$$
--   In particular its output is globally continuous and agrees with $R$-affine functions on a finite polyhedral cover of all real inputs. This gives the reverse inclusion using the independently defined network evaluator, rather than building CPWL membership into representability.
--
--   Differences from the source:
--   - encoding: real inputs, field R containing the rationals, finite polyhedral partition and two hidden layers → Subfield ℝ, EuclideanSpace ℝ (Fin n), finite closed polyhedral cover and three affine-map evaluator; reason: every real subfield contains ℚ; common hyperplane refinement identifies the cover with a partition; widths remain arbitrary finite naturals
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026), p. 2, Section 1, CPWL observation and Eq. (1)

import Definitions.Def_TwoReLULayers_DepthCollapse_Construction

namespace TwoReLULayers.DepthCollapse

theorem network_geometric_cpwl {n : ℕ} (hn : 1 ≤ n) (R : Subfield ℝ)
    (N : Network2 R n) : N.eval ∈ CPWL R n := by sorry

end TwoReLULayers.DepthCollapse
