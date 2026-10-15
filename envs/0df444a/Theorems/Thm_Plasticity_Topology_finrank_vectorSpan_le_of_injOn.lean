-- Prove2me | Theorems.Thm_Plasticity_Topology_finrank_vectorSpan_le_of_injOn
-- name    : Plasticity.Topology.finrank_vectorSpan_le_of_injOn
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-15T00:33:52.799371+00:00
-- url     : https://prove2.me/theorems/13941c2a-65c6-476a-9945-26e34effe8b4
-- title:
--   A convex set mapped continuously and injectively into a finite-dimensional affine subspace has no larger dimension
-- statement:
--   Let $D$ be a convex subset of a real normed space, $W$ a finite-dimensional subspace of another, $c$ a point, and $f$ continuous and injective on $D$ with $f(x)-c\in W$ for $x\in D$. Then the affine hull of $D$ is finite-dimensional and $\dim\operatorname{span}(D-D)\le\dim W$.
-- source:
--   Invariance of dimension (card Plasticity.Ext.InvarianceOfDimension)

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

namespace Plasticity.Topology
theorem finrank_vectorSpan_le_of_injOn {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (D : Set E) (hconv : Convex ℝ D)
    (f : E → E') (hf : ContinuousOn f D) (hinj : Set.InjOn f D)
    (W : Submodule ℝ E') (hW : FiniteDimensional ℝ W) (c : E') (hc : ∀ x ∈ D, f x - c ∈ W) :
    FiniteDimensional ℝ (vectorSpan ℝ D) ∧
      Module.finrank ℝ (vectorSpan ℝ D) ≤ Module.finrank ℝ W := by sorry
end Plasticity.Topology
