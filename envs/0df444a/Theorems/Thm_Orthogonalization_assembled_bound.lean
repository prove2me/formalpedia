-- Prove2me | Theorems.Thm_Orthogonalization_assembled_bound
-- name    : Orthogonalization.assembled_bound
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:53:57.08524+00:00
-- url     : https://prove2.me/theorems/347d1533-1c86-4d8d-a1ce-2e35b5e0b1fa
-- title:
--   Step F3 of the proof of Theorem 1.2 in the finite case. Given the isometry data (w_i) of Lemma 3.2 for a POVM (a_i) and the commuting projections (q_i) of Lemma 3.1, the…
-- statement:
--   A statement of the module `MIPRE.Background.Orthonormalization.Orthogonalization.Assembly` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). ### The assembled projections
--
--   The module is vendored read-only from the `orthogonalization` development of [vidick/commuting-repetition](https://github.com/vidick/commuting-repetition) (Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-repetition.py`.
--
--   **Step F3 of the proof of Theorem 1.2 in the finite case.** Given the
--   isometry data `(w_i)` of Lemma 3.2 for a POVM `(a_i)` and the commuting
--   projections `(q_i)` of Lemma 3.1, the assembled PVM `p_i = w_i* w_i` satisfies
--   `φ (∑ i, |a_i - p_i|²) < 9 ε` whenever `φ (∑ i, a_i²) > 1 - ε` and
--   `φ (∑ i, q_i a_i) ≥ 1 - ε`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open Orthogonalization
--   open scoped ComplexOrder BigOperators
--   variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
--   variable {ι : Type*} [Fintype ι] [DecidableEq ι]
--
--   theorem Orthogonalization.assembled_bound (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
--       (hφ : ∀ x : H →L[ℂ] H, 0 ≤ φ (star x * x)) (hφ1 : φ 1 = 1)
--       (a q w : ι → H →L[ℂ] H) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1)
--       (hq : ∀ i, IsStarProjection (q i)) (hqa : ∀ i, Commute (q i) (a i))
--       (hw : IsometryData a q w) (ε : ℝ) (hε : 1 - ε < (φ (∑ i, a i * a i)).re)
--       (hlarge : 1 - ε ≤ (φ (∑ i, q i * a i)).re) :
--       (φ (∑ i, star (a i - assembledPVM w i) * (a i - assembledPVM w i))).re < 9 * ε
--   ```
--
--   **Formalization Note** `Orthogonalization.assembled_bound` is declared in `MIPRE/Background/Orthonormalization/Orthogonalization/Assembly.lean`, lines 430–452. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/Orthonormalization/Orthogonalization/Assembly.lean#L430-L452

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.NNReal.Star
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.SetLike.Basic
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.Defs
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_Positivity
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_PhiNorm
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_IsometryData
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_Assembly

open Orthogonalization
open scoped ComplexOrder BigOperators
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Orthogonalization.assembled_bound (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hφ : ∀ x : H →L[ℂ] H, 0 ≤ φ (star x * x)) (hφ1 : φ 1 = 1)
    (a q w : ι → H →L[ℂ] H) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1)
    (hq : ∀ i, IsStarProjection (q i)) (hqa : ∀ i, Commute (q i) (a i))
    (hw : IsometryData a q w) (ε : ℝ) (hε : 1 - ε < (φ (∑ i, a i * a i)).re)
    (hlarge : 1 - ε ≤ (φ (∑ i, q i * a i)).re) :
    (φ (∑ i, star (a i - assembledPVM w i) * (a i - assembledPVM w i))).re < 9 * ε := by sorry
