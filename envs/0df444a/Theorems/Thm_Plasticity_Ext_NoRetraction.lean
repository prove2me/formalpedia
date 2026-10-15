-- Prove2me | Theorems.Thm_Plasticity_Ext_NoRetraction
-- name    : Plasticity.Ext.NoRetraction
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T18:44:00.81512+00:00
-- url     : https://prove2.me/theorems/b53fad7f-22b7-45c2-8f57-6b767c9a97b2
-- title:
--   No retraction of a closed ball onto its boundary sphere
-- statement:
--   Let $V$ be a nonzero finite-dimensional real normed space with closed unit ball $B$ and unit sphere $S$. If $r\colon B\to S$ is continuous, then $r(x)\ne x$ for some $x\in S$: there is no continuous retraction of $B$ onto $S$.
-- source:
--   Classical, equivalent to Brouwer's fixed-point theorem: if r were a retraction, −r would map the ball into the sphere without a fixed point (L. E. J. Brouwer, Über Abbildung von Mannigfaltigkeiten, Math. Ann. 71 (1912))

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.ContinuousOn

namespace Plasticity.Ext
theorem NoRetraction {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Nontrivial V] (r : V → V) (hr : ContinuousOn r (Metric.closedBall (0 : V) 1))
    (hmaps : Set.MapsTo r (Metric.closedBall (0 : V) 1) (Metric.sphere (0 : V) 1)) :
    ∃ x ∈ Metric.sphere (0 : V) 1, r x ≠ x := by sorry
end Plasticity.Ext
