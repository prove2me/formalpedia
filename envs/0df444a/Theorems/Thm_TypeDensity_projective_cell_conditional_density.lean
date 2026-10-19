-- Prove2me | Theorems.Thm_TypeDensity_projective_cell_conditional_density
-- name    : TypeDensity.projective_cell_conditional_density
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:52:44.347981+00:00
-- url     : https://prove2.me/theorems/6087b5c8-e8c3-4df2-a98a-40cf0f2b74a4
-- title:
--   The conditional density of a projective cell inside the primitive locus is the value of `1 / projectiveNormalizer n` at `q`.
-- statement:
--   The conditional density of a projective cell inside the primitive locus is the value of `1 / projectiveNormalizer n` at `q`.
-- source:
--   TypeDensity/Unramified/FrobeniusDescent.lean#L111-L161

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_primitive_locus_mass
import Theorems.Thm_TypeDensity_projective_cell_mass
import Theorems.Thm_TypeDensity_projective_normalizer_eval
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Henselian
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.projective_cell_conditional_density (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ)
    (v : Fin (n + 1) → IsLocalRing.ResidueField O) (hv : v ≠ 0) :
    coefficientMeasure O (n+1) (projectiveCell O n v) /
        coefficientMeasure O (n+1) {a : Fin (n+1) → O | primitive O a} =
      densityValue (Expr.inv (projectiveNormalizer n)) (Nat.card (IsLocalRing.ResidueField O)) := by sorry
