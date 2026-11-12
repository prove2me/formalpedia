-- Prove2me | Theorems.Thm_TypeDensity_universal_type_laws
-- name    : TypeDensity.universal_type_laws
-- status  : Proved
-- author  : @asving
-- created : 2026-11-11T18:53:51.89143+00:00
-- url     : https://prove2.me/theorems/b04ed4ee-9de3-43e3-8c6a-fbae1543ec0c
-- title:
--   Theorem 1.1 (universal type laws), packaged: rational functions `A, B, R ∈ ℚ(q)`, regular and nonnegative at prime powers, give the monic, cluster and projective probabilities over every complete DVR.
-- statement:
--   **Theorem 1.1 (universal type laws), packaged.** For every degree `n` and every type `σ` there are rational functions `A, B, R ∈ ℚ(q)` — namely the rational functions of `monicExpr n σ`, `clusterExpr n σ`, `projectiveExpr n σ` — such that
--
--   * `A`, `B`, `R` are regular at every prime power, and their values there are nonnegative;
--   * over every complete discrete valuation ring `O` with finite residue field `k` (any characteristic, any ramification; adic topology, Borel σ-algebra, normalized Haar measure), with `q = |k|`, the values `A(q)`, `B(q)`, `R(q)` are nonnegative rational numbers and the monic, cluster and projective probabilities of type `σ` are `A(q)`, `B(q)`, `R(q)`.
--
--   Each probability clause has the form `0 ≤ r ∧ density = ENNReal.ofReal r`. The two parts together determine the density exactly: `ENNReal.ofReal` is injective on nonnegative reals, so no clamping at `0` is possible, and the density is finite. The values are those of Mathlib's `RatFunc.eval`, so the convention `0⁻¹ = 0` of `Expr.eval` does not enter the statement.
-- source:
--   TypeDensity/Corollaries/RationalForm.lean#L100-L150

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Cluster_Defs
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Formula_FiniteFieldCounts
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Formula_PatternCounts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Definitions.Def_TypeDensity_Surfaces_TruncatedSeries
import Definitions.Def_TypeDensity_Blowup_TwoChartCurveData
import Definitions.Def_TypeDensity_Surfaces_ConcreteAtlas
import Definitions.Def_TypeDensity_Recursion_Members
import Definitions.Def_TypeDensity_Measure_MemberCharts
import Definitions.Def_TypeDensity_Recursion_Termination
import Definitions.Def_TypeDensity_Recursion_OrderDefect
import Definitions.Def_TypeDensity_Assembly_NullBridges
import Definitions.Def_TypeDensity_Assembly_TypeEvents
import Definitions.Def_TypeDensity_Assembly_MonicCells
import Definitions.Def_TypeDensity_Blowup_DivisorPoints
import Definitions.Def_TypeDensity_Measure_MemberBoxes
import Definitions.Def_TypeDensity_Recursion_ChildMembers
import Definitions.Def_TypeDensity_Recursion_RootCellLaw
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_main_dvr_cluster
import Theorems.Thm_TypeDensity_cluster_formula_regular
import Theorems.Thm_TypeDensity_monicExpr_eval_nonneg
import Theorems.Thm_TypeDensity_projectiveExpr_eval_nonneg
import Theorems.Thm_TypeDensity_clusterExpr_eval_nonneg
import Theorems.Thm_TypeDensity_cluster_rational_eval
import Theorems.Thm_TypeDensity_finite_field_card_primePower
import Theorems.Thm_TypeDensity_global_rational_eval
import Theorems.Thm_TypeDensity_global_formula_regular
import Theorems.Thm_TypeDensity_main_dvr
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.Algebra.Group.NatPowAssoc
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Log
set_option autoImplicit false

open TypeDensity
open scoped ENNReal

theorem TypeDensity.universal_type_laws (n : ℕ) (σ : FactorType) :
    ∃ A B R : RatFunc ℚ,
      A = (monicExpr n σ).rational ∧ B = (clusterExpr n σ).rational ∧
      R = (projectiveExpr n σ).rational ∧
      (∀ q : ℕ, PrimePower q → RegularAt A q ∧ RegularAt B q ∧ RegularAt R q) ∧
      (∀ q : ℕ, PrimePower q →
        0 ≤ RatFunc.eval (RingHom.id ℚ) (q : ℚ) A ∧ 0 ≤ RatFunc.eval (RingHom.id ℚ) (q : ℚ) B ∧
        0 ≤ RatFunc.eval (RingHom.id ℚ) (q : ℚ) R) ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
        [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
        [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O],
        IsAdic (IsLocalRing.maximalIdeal O) →
          (0 ≤ RatFunc.eval (RingHom.id ℚ) ((Nat.card (IsLocalRing.ResidueField O) : ℕ) : ℚ) A ∧
            monicDensity O n σ = ENNReal.ofReal ((RatFunc.eval (RingHom.id ℚ)
              ((Nat.card (IsLocalRing.ResidueField O) : ℕ) : ℚ) A : ℚ) : ℝ)) ∧
          (0 ≤ RatFunc.eval (RingHom.id ℚ) ((Nat.card (IsLocalRing.ResidueField O) : ℕ) : ℚ) B ∧
            clusterDensity O n σ = ENNReal.ofReal ((RatFunc.eval (RingHom.id ℚ)
              ((Nat.card (IsLocalRing.ResidueField O) : ℕ) : ℚ) B : ℚ) : ℝ)) ∧
          (0 ≤ RatFunc.eval (RingHom.id ℚ) ((Nat.card (IsLocalRing.ResidueField O) : ℕ) : ℚ) R ∧
            projectiveDensity O n σ = ENNReal.ofReal ((RatFunc.eval (RingHom.id ℚ)
              ((Nat.card (IsLocalRing.ResidueField O) : ℕ) : ℚ) R : ℚ) : ℝ)) := by sorry
