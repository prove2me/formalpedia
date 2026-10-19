-- Prove2me | Theorems.Thm_Orthogonalization_FinDim_exists_isometry_completion
-- name    : Orthogonalization.FinDim.exists_isometry_completion
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:53:41.974592+00:00
-- url     : https://prove2.me/theorems/63c0ac15-965b-4dc8-ae34-630d0c62d166
-- title:
--   Isometric completion
-- statement:
--   A statement of the module `MIPRE.Background.Orthonormalization.Orthogonalization.FinDim.Isometry` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization).
--
--   The module is vendored read-only from the `orthogonalization` development of [vidick/commuting-repetition](https://github.com/vidick/commuting-repetition) (Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-repetition.py`.
--
--   **Isometric completion.**
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open scoped InnerProductSpace ComplexOrder
--   open Module ContinuousLinearMap
--   variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
--
--   theorem Orthogonalization.FinDim.exists_isometry_completion (T : H →L[ℂ] K) (s : H →L[ℂ] H)
--       (hs : IsSelfAdjoint s) (hs0 : 0 ≤ s) (hT : adjoint T ∘L T = s ∘L s)
--       (L : Submodule ℂ K) (hTL : LinearMap.range (T : H →ₗ[ℂ] K) ≤ L) (hL : finrank ℂ L = finrank ℂ H) :
--       ∃ u : H →L[ℂ] K, adjoint u ∘L u = 1 ∧ u ∘L adjoint u = L.starProjection ∧
--         u ∘L s = T
--   ```
--
--   **Formalization Note** `Orthogonalization.FinDim.exists_isometry_completion` is declared in `MIPRE/Background/Orthonormalization/Orthogonalization/FinDim/Isometry.lean`, lines 119–252. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/Orthonormalization/Orthogonalization/FinDim/Isometry.lean#L119-L252

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.FunLike.IsApply
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Data.SetLike.Basic
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Notation
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs

open scoped InnerProductSpace ComplexOrder
open Module ContinuousLinearMap
set_option autoImplicit true
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]

theorem Orthogonalization.FinDim.exists_isometry_completion (T : H →L[ℂ] K) (s : H →L[ℂ] H)
    (hs : IsSelfAdjoint s) (hs0 : 0 ≤ s) (hT : adjoint T ∘L T = s ∘L s)
    (L : Submodule ℂ K) (hTL : LinearMap.range (T : H →ₗ[ℂ] K) ≤ L) (hL : finrank ℂ L = finrank ℂ H) :
    ∃ u : H →L[ℂ] K, adjoint u ∘L u = 1 ∧ u ∘L adjoint u = L.starProjection ∧
      u ∘L s = T := by sorry
