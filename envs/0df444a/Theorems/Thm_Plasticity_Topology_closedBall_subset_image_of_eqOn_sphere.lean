-- Prove2me | Theorems.Thm_Plasticity_Topology_closedBall_subset_image_of_eqOn_sphere
-- name    : Plasticity.Topology.closedBall_subset_image_of_eqOn_sphere
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-15T00:33:52.838843+00:00
-- url     : https://prove2.me/theorems/501b45a7-15d3-4787-98a6-e0ecf6116808
-- title:
--   A continuous self-map of a closed ball fixing its boundary sphere is onto the ball
-- statement:
--   Let $V$ be a finite-dimensional real normed space, and let $g$ be continuous on the closed unit ball $B$ of $V$ with $g(z)=z$ for every unit vector $z$. Then $B\subseteq g(B)$.
-- source:
--   Classical consequence of the no-retraction theorem (card Plasticity.Ext.NoRetraction): a missed point would give a retraction of B onto its sphere

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.ContinuousOn

namespace Plasticity.Topology
theorem closedBall_subset_image_of_eqOn_sphere {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (g : V → V) (hg : ContinuousOn g (Metric.closedBall (0 : V) 1))
    (hid : ∀ z ∈ Metric.sphere (0 : V) 1, g z = z) :
    Metric.closedBall (0 : V) 1 ⊆ g '' Metric.closedBall (0 : V) 1 := by sorry
end Plasticity.Topology
