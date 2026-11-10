-- Prove2me | Theorems.Thm_TwoReLULayers_DepthCollapse_paramid_geometry
-- name    : TwoReLULayers.DepthCollapse.paramid_geometry
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:35:16.674206+00:00
-- url     : https://prove2.me/theorems/87d76c55-5b91-466a-b217-bfe31781b08c
-- title:
--   Claim 19 — Geometry of the explicit paramids
-- statement:
--   Let $n\ge2$, $v\in[n]$, let $\pi$ order $[n]\setminus\{v\}$, and let $M\subseteq\{2,\ldots,n-1\}$ be marked positions. The explicitly defined $K_{v,\pi,M}$ is a paramid, and there is a parallelepiped $B$ such that
--   $$\dim B=n-2,\qquad B\subseteq H_0\cap\{y:y_v=-1\},\qquad K_{v,\pi,M}=\operatorname{conv}(\{0\}\cup B).$$
--   The base is represented by $n-2$ independent edges. At $n=2$ it is a point. This records its exact geometry and the specified apex.
--
--   Differences from the source:
--   - encoding: finite Euclidean coordinates and finite index families → EuclideanSpace ℝ (Fin n), Fin k and pointwise function identities; reason: canonical coordinate identification and reindexing preserve every source instance
--   - encoding: vertex labels 1,...,n and marked positions 2,...,n-1 → zero-based Fin labels, bijective Order v and positive-valued marked positions; reason: subtracting one from labels and positions is a bijective reindexing; position one remains unconstrained
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026), p. 22, Claim 19

import Definitions.Def_TwoReLULayers_DepthCollapse_Construction

namespace TwoReLULayers.DepthCollapse

theorem paramid_geometry {n : ℕ} (hn : 2 ≤ n) (v : Fin n) (π : Order v)
    (M : Finset (Fin (n - 1))) (hM : M ⊆ markedPositions n) :
    IsParamid (paramidK v π M) ∧
    ∃ a : E n, ∃ e : Fin (n - 2) → E n,
      LinearIndependent ℝ e ∧ affineDim (box a e) = n - 2 ∧
      box a e ⊆ {y | y ∈ zeroHyperplane n ∧ y v = -1} ∧
      paramidK v π M = convexHull ℝ (insert (0 : E n) (box a e)) := by sorry

end TwoReLULayers.DepthCollapse
