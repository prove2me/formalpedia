-- Prove2me | Theorems.Thm_TwoReLULayers_DepthCollapse_network_precomposition
-- name    : TwoReLULayers.DepthCollapse.network_precomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:35:17.3333+00:00
-- url     : https://prove2.me/theorems/581a2d7c-27d6-440c-a248-444e45998bad
-- title:
--   Affine precomposition preserves two hidden layers
-- statement:
--   For a real subfield $R$ and positive dimensions $n,m$, let $A:E_n\to E_m$ be $R$-affine and let $f\in\operatorname{ReLU2}(R,m)$. Then
--   $$f\circ A\in\operatorname{ReLU2}(R,n).$$
--   The affine map is absorbed without introducing an additional hidden layer. This is the closure needed to use the affine arguments in equation (2).
--
--   Differences from the source:
--   - encoding: finite Euclidean coordinates and finite index families → EuclideanSpace ℝ (Fin n), Fin k and pointwise function identities; reason: canonical coordinate identification and reindexing preserve every source instance
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026), p. 2, Section 1, Eq. (2), affine-argument depth reduction

import Definitions.Def_TwoReLULayers_DepthCollapse_Construction

namespace TwoReLULayers.DepthCollapse

theorem network_precomposition {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (R : Subfield ℝ) (A : AffineR R n m) (f : E m → ℝ) (hf : f ∈ ReLU2 R m) :
    (fun x => f (affineEval A x)) ∈ ReLU2 R n := by sorry

end TwoReLULayers.DepthCollapse
