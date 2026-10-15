-- Prove2me | Theorems.Thm_Plasticity_Topology_isOpen_image_of_injOn_of_finrank_eq
-- name    : Plasticity.Topology.isOpen_image_of_injOn_of_finrank_eq
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-15T00:33:52.58624+00:00
-- url     : https://prove2.me/theorems/ac4835c3-cde1-452d-a2e4-8f73a0b9c386
-- title:
--   Invariance of domain between finite-dimensional normed spaces of equal dimension
-- statement:
--   Let $V,W$ be finite-dimensional real normed spaces of the same dimension, $U\subseteq V$ open, and $f$ continuous and injective on $U$. Then $f(U)$ is open in $W$.
-- source:
--   L. E. J. Brouwer, Beweis der Invarianz des n-dimensionalen Gebiets, Math. Ann. 71 (1912); from the card Plasticity.Ext.InvarianceOfDomain

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.ContinuousOn

namespace Plasticity.Topology
theorem isOpen_image_of_injOn_of_finrank_eq {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (hdim : Module.finrank ℝ V = Module.finrank ℝ W)
    (U : Set V) (hU : IsOpen U) (f : V → W) (hf : ContinuousOn f U) (hinj : Set.InjOn f U) :
    IsOpen (f '' U) := by sorry
end Plasticity.Topology
