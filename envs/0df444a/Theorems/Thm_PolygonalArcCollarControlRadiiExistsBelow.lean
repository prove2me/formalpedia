-- Prove2me | Theorems.Thm_PolygonalArcCollarControlRadiiExistsBelow
-- name    : PolygonalArcCollarControlRadiiExistsBelow
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T23:54:46.396221+00:00
-- url     : https://prove2.me/theorems/4f07b453-8f41-405c-af9a-c79165fa4f96
-- title:
--   PolygonalArcCollarControlRadiiExistsBelow
-- statement:
--   For a polygonal arc, positive tolerance, and positive endpoint-isolation radii, there exist positive collar-control radii smaller than the tolerance, with endpoint radii below the isolation radii and the required endpoint-ball disjointness properties.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarControlRadiiExistsBelow.lean#L1-304

import Definitions.Def_PolygonalArcCollarControlRadii
import Definitions.Def_PolygonalArcEndpointIsolation

import Mathlib.Tactic

open Classical
noncomputable section

lemma PolygonalArcCollarControlRadiiExistsBelow (γ : PolygonalArc)
    (η r₀ r₁ : ℝ) :
    0 < η →
      0 < r₀ →
        0 < r₁ →
          PolygonalArcEndpointIsolation γ r₀ r₁ →
            let hsource : 0 < γ.vertices.length := by
              have hlen := γ.length_ge_two
              omega
            let htarget : γ.vertices.length - 1 < γ.vertices.length := by
              have hlen := γ.length_ge_two
              omega
            ∃ controlRadii : PolygonalArcCollarControlRadii γ η,
              controlRadii.radius ⟨0, hsource⟩ < r₀ ∧
                controlRadii.radius ⟨γ.vertices.length - 1, htarget⟩ < r₁ ∧
                  (∀ i : Fin γ.vertices.length, i.1 ≠ 0 →
                    Disjoint
                      (Metric.ball γ.vertices[i.1] (controlRadii.radius i))
                      (Metric.ball γ.source r₀)) ∧
                    (∀ i : Fin γ.vertices.length,
                      i.1 + 1 ≠ γ.vertices.length →
                        Disjoint
                          (Metric.ball γ.vertices[i.1] (controlRadii.radius i))
                          (Metric.ball γ.target r₁)) := by sorry
