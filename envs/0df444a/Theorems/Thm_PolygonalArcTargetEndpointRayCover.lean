-- Prove2me | Theorems.Thm_PolygonalArcTargetEndpointRayCover
-- name    : PolygonalArcTargetEndpointRayCover
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T22:18:02.435739+00:00
-- url     : https://prove2.me/theorems/be379473-8250-4f09-b354-5bf389b23f57
-- title:
--   Terminal ray cover near a polygonal-arc target endpoint
-- statement:
--   For every polygonal arc $\gamma$, there is a positive radius $r$ such that every point of the carrier inside the target ball $B(\gamma.target,r)$ lies on the closed ray from the target through the penultimate vertex:
--   $$
--   B(\gamma.target,r)\cap\gamma.carrier
--   \subseteq
--   \left\{\gamma.target+cigl(\gamma_{n-2}-\gamma.targetigr):c\ge0ight\}.
--   $$
--
--   This identifies all arc points sufficiently close to the target with the single terminal ray that is removed from the slit disk.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcTargetEndpointRayCover.lean#L1-31

import Definitions.Def_PolygonalArc

open Classical
noncomputable section

lemma PolygonalArcTargetEndpointRayCover (γ : PolygonalArc) :
    ∃ r : ℝ, 0 < r ∧
      (let hprev : γ.vertices.length - 2 < γ.vertices.length := by
        have hlen := γ.length_ge_two
        omega
       Metric.ball γ.target r ∩ γ.carrier ⊆
        {x | ∃ c : ℝ, 0 ≤ c ∧
          x = γ.target +
            c • (γ.vertices[γ.vertices.length - 2]'hprev - γ.target)}) := by sorry
