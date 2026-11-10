-- Prove2me | Theorems.Thm_TwoReLULayers_DepthCollapse_network_linear_combination
-- name    : TwoReLULayers.DepthCollapse.network_linear_combination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:35:24.799485+00:00
-- url     : https://prove2.me/theorems/485af46b-71f1-4e04-9beb-04c4536427fa
-- title:
--   Parallel closure under finite field-linear combinations
-- statement:
--   Let $R\subseteq\mathbb R$ be a subfield, $n\ge1$, and let $f_i:E_n\to\mathbb R$ have two-hidden-layer representations over $R$. For any finite family of coefficients $c_i\in R$,
--   $$\sum_i c_i f_i\in\operatorname{ReLU2}(R,n).$$
--   This is closure within the same two hidden layers, and includes negative coefficients and the empty sum. The widths may grow with the finite family.
--
--   Differences from the source:
--   - encoding: finite Euclidean coordinates and finite index families → EuclideanSpace ℝ (Fin n), Fin k and pointwise function identities; reason: canonical coordinate identification and reindexing preserve every source instance
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026), p. 2, Section 1, finite-sum depth reduction following Eq. (2)

import Definitions.Def_TwoReLULayers_DepthCollapse_Construction

namespace TwoReLULayers.DepthCollapse

theorem network_linear_combination {n k : ℕ} (hn : 1 ≤ n) (R : Subfield ℝ)
    (c : Fin k → R) (f : Fin k → E n → ℝ) (hf : ∀ i, f i ∈ ReLU2 R n) :
    (fun x => ∑ i, (c i : ℝ) * f i x) ∈ ReLU2 R n := by sorry

end TwoReLULayers.DepthCollapse
