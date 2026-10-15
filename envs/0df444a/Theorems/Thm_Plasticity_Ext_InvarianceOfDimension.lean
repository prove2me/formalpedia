-- Prove2me | Theorems.Thm_Plasticity_Ext_InvarianceOfDimension
-- name    : Plasticity.Ext.InvarianceOfDimension
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T18:43:59.333415+00:00
-- url     : https://prove2.me/theorems/f36a7b41-99ad-46b1-8de7-20ce95a82bdb
-- title:
--   Invariance of dimension
-- statement:
--   Let $V,W$ be finite-dimensional real normed spaces, $U\subseteq V$ a nonempty open set, and $f\colon U\to W$ continuous and injective. Then $\dim V\le\dim W$.
-- source:
--   L. E. J. Brouwer, Beweis der Invarianz der Dimensionenzahl, Math. Ann. 70 (1911); here a consequence of invariance of domain (card Plasticity.Ext.InvarianceOfDomain)

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.ContinuousOn

namespace Plasticity.Ext
theorem InvarianceOfDimension {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (U : Set V) (hU : IsOpen U) (hne : U.Nonempty) (f : V → W)
    (hf : ContinuousOn f U) (hinj : Set.InjOn f U) :
    Module.finrank ℝ V ≤ Module.finrank ℝ W := by sorry
end Plasticity.Ext
