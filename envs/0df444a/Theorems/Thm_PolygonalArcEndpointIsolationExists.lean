-- Prove2me | Theorems.Thm_PolygonalArcEndpointIsolationExists
-- name    : PolygonalArcEndpointIsolationExists
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T22:17:49.647142+00:00
-- url     : https://prove2.me/theorems/553ac6af-6240-4c69-9d8c-9baa7c318743
-- title:
--   Endpoint isolation radii for a polygonal arc
-- statement:
--   Every polygonal arc $\gamma$ admits positive radii $r_0$ and $r_1$ such that the closed endpoint balls are disjoint, each endpoint ball meets the carrier only on the corresponding first or last segment, and each radius is smaller than the length of that endpoint segment. In symbols,
--   $$
--   \exists r_0,r_1>0,\quad \operatorname{PolygonalArcEndpointIsolation}(\gamma,r_0,r_1).
--   $$
--
--   The result supplies the endpoint control data used by both the tail-source and terminal-slit-disk constructions.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcEndpointIsolationExists.lean#L1-150

import Definitions.Def_PolygonalArcEndpointIsolation

open Classical
noncomputable section

lemma PolygonalArcEndpointIsolationExists (γ : PolygonalArc) :
    ∃ r₀ r₁ : ℝ, PolygonalArcEndpointIsolation γ r₀ r₁ := by sorry
