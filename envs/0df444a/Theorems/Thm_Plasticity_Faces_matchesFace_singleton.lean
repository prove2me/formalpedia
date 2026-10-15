-- Prove2me | Theorems.Thm_Plasticity_Faces_matchesFace_singleton
-- name    : Plasticity.Faces.matchesFace_singleton
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-15T00:33:54.945524+00:00
-- url     : https://prove2.me/theorems/d5375000-1dac-4f43-b9b2-34ad4aa80be5
-- title:
--   A one-point face of the target ball is carried onto a one-point face
-- statement:
--   Let $F\colon B_X\to B_Y$ be a nonexpansive bijection of the unit balls of real normed spaces, and let $\{e\}$ be a sphere face of $B_Y$, that is, $e$ is an extreme point of $B_Y$ of norm one. Then `MatchesFace F {e}` holds: the preimage of $e$ is a single extreme point $x$ of $B_X$ of norm one, $F(-x)=-e$, and $F(tx)=te$ for $0\le t\le1$.
--   This is the dimension-0 case of the face theorem (card `Plasticity.Faces.matchesFace_of_finiteDimensional`).
-- source:
--   O. Zavarzina, Non-expansive bijections between unit balls of Banach spaces, Ann. Funct. Anal. 9 (2018), Theorem 2.3 (arXiv:1704.06961), through the cards Plasticity.BallMap.*; this repository's claims U01 and F17 (claims/u.md, claims/f.md)

import Definitions.Def_Plasticity_Faces
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.Faces
theorem matchesFace_singleton {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hbij : Set.BijOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (e : Y) (he : IsSphereFace ({e} : Set Y)) :
    MatchesFace F {e} := by sorry
end Plasticity.Faces
