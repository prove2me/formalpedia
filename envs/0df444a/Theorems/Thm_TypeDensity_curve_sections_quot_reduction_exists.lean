-- Prove2me | Theorems.Thm_TypeDensity_curve_sections_quot_reduction_exists
-- name    : TypeDensity.curve_sections_quot_reduction_exists
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:42.900836+00:00
-- url     : https://prove2.me/theorems/fbf6ce43-9fc5-4b64-ae54-0d64b3ffe7a2
-- title:
--   Reduction maps between consecutive levels of the curve sections modulo the curve lattices.
-- statement:
--   Reduction maps exist between consecutive levels of the curve sections modulo the curve lattices.
-- source:
--   TypeDensity/Blowup/CurveOrders.lean#L194-L218

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Formula_FiniteFieldCounts
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_curve_lattices_antitone
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
import Mathlib.Topology.Algebra.MvPolynomial
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
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.curve_sections_quot_reduction_exists (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d : ℕ) (G : GluedGenerators R t x beta d) (j : ℕ) :
    ∃ ρ : curveSectionsQuot R t x beta G (j+1) →ₗ[R] curveSectionsQuot R t x beta G j, ∀ q :
        curveSectionsQuot R t x beta G (j+1), ∀ p : BlowupChart R t x × BlowupChart R x t,
        (q : (BlowupChart R t x × BlowupChart R x t) ⧸ curveIdealLattice R t x beta G (j+1)) =
        (curveIdealLattice R t x beta G (j+1)).mkQ p → ((ρ q : curveSectionsQuot R t x beta G j) :
        (BlowupChart R t x × BlowupChart R x t) ⧸ curveIdealLattice R t x beta G j) =
        (curveIdealLattice R t x beta G j).mkQ p := by sorry
