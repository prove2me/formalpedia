-- Prove2me | Theorems.Thm_TwoReLULayers_DepthCollapse_paramid_network
-- name    : TwoReLULayers.DepthCollapse.paramid_network
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:35:14.949665+00:00
-- url     : https://prove2.me/theorems/866b5bec-c592-4d84-9a2e-f0c155dab5d1
-- title:
--   Paramid support formula and actual two-hidden-layer realization
-- statement:
--   Let $R\subseteq\mathbb R$ be a subfield, $n\ge1$, and let $a,\gamma,e_1,\ldots,e_k\in R^n$ with independent $e_i$. For the paramid $P=\operatorname{conv}(\{\gamma\}\cup(a+\sum_i[0,e_i]))$,
--   $$h_P(x)=\max\{\langle\gamma,x\rangle,\ \langle a,x\rangle+\sum_i\max(0,\langle e_i,x\rangle)\},\qquad h_P\in\operatorname{ReLU2}(R,n).$$
--   The second clause means an actual network with three affine maps and two intervening ReLU activations, all coefficients in $R$, including the signed linear quantities in the displayed formula. This is the source's segment-endpoint formula written using a translation and edges; setting $a=\sum_i a_i$ and $e_i=b_i-a_i$ recovers equation (3). A point base is allowed.
--
--   Differences from the source:
--   - encoding: finite Euclidean coordinates and finite index families → EuclideanSpace ℝ (Fin n), Fin k and pointwise function identities; reason: canonical coordinate identification and reindexing preserve every source instance
--   - encoding: Minkowski sum of segments [a_i,b_i] → translated box a + sum [0,e_i] with independent edges; reason: a=sum a_i and e_i=b_i-a_i give the identical parallelepiped; any translated box has such a segment representation, including a singleton segment for a point base
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026), p. 4, Section 1.1, Eq. (3) and two-layer paramid discussion

import Definitions.Def_TwoReLULayers_DepthCollapse_Construction

namespace TwoReLULayers.DepthCollapse

theorem paramid_network {n k : ℕ} (hn : 1 ≤ n) (R : Subfield ℝ)
    (a apex : E n) (e : Fin k → E n) (he : LinearIndependent ℝ e)
    (ha : Over R a) (hapex : Over R apex) (hedges : ∀ i, Over R (e i)) :
    (∀ x : E n, support (convexHull ℝ (insert apex (box a e))) x =
      max (dot apex x) (dot a x + ∑ i, max 0 (dot (e i) x))) ∧
    support (convexHull ℝ (insert apex (box a e))) ∈ ReLU2 R n := by sorry

end TwoReLULayers.DepthCollapse
