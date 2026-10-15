-- Prove2me | Theorems.Thm_Plasticity_Topology_mapsTo_intrinsicInterior_of_injOn
-- name    : Plasticity.Topology.mapsTo_intrinsicInterior_of_injOn
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-15T00:33:52.760985+00:00
-- url     : https://prove2.me/theorems/e4d37b36-ec73-4cd3-a060-551245d6de57
-- title:
--   Continuous injections between convex sets of equal finite dimension preserve relative interiors
-- statement:
--   Let $D$ and $C$ be subsets of real normed spaces with finite-dimensional affine hulls of the same dimension, and let $f$ be continuous and injective on $D$ with $f(D)\subseteq C$. Then $f$ maps the relative interior of $D$ into the relative interior of $C$.
-- source:
--   Invariance of domain (card Plasticity.Topology.isOpen_image_of_injOn_of_finrank_eq)

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Intrinsic

namespace Plasticity.Topology
theorem mapsTo_intrinsicInterior_of_injOn {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (D : Set E) (C : Set E')
    (hD : FiniteDimensional ℝ (vectorSpan ℝ D)) (hC : FiniteDimensional ℝ (vectorSpan ℝ C))
    (hdim : Module.finrank ℝ (vectorSpan ℝ D) = Module.finrank ℝ (vectorSpan ℝ C))
    (f : E → E') (hf : ContinuousOn f D) (hinj : Set.InjOn f D) (hmaps : Set.MapsTo f D C) :
    Set.MapsTo f (intrinsicInterior ℝ D) (intrinsicInterior ℝ C) := by sorry
end Plasticity.Topology
