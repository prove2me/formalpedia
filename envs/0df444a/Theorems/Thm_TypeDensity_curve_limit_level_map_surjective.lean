-- Prove2me | Theorems.Thm_TypeDensity_curve_limit_level_map_surjective
-- name    : TypeDensity.curve_limit_level_map_surjective
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:00:22.739216+00:00
-- url     : https://prove2.me/theorems/e51c4d9c-9ef0-49e2-a572-0678e0459a41
-- title:
--   The projection from the curve order limit to the level-`J` quotient of curve sections is surjective.
-- statement:
--   The projection from the curve order limit to the level-`J` quotient of curve sections is surjective.
-- source:
--   TypeDensity/Blowup/CurveSections.lean#L430-L492

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
import Definitions.Def_TypeDensity_Surfaces_TruncatedSeries
import Theorems.Thm_TypeDensity_curve_lattices_antitone
import Theorems.Thm_TypeDensity_curve_sections_quot_reduction_exists
import Theorems.Thm_TypeDensity_two_chart_layer_correction
import Theorems.Thm_TypeDensity_beta_right_chartBase
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
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.Algebra.Group.NatPowAssoc
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.curve_limit_level_map_surjective (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d : ℕ) (G : GluedGenerators R t x beta d)
    (hreg : RegularParameterPair R t x) (J : ℕ)
    (π : CurveOrderLimit R t x beta G →ₗ[R] curveSectionsQuot R t x beta G J)
    (hπ : ∀ p : curveThreads R t x beta G,
      ((π (curveLimitMk R t x beta G p) : curveSectionsQuot R t x beta G J) :
      (BlowupChart R t x × BlowupChart R x t) ⧸ curveIdealLattice R t x beta G J) =
      (curveIdealLattice R t x beta G J).mkQ (p.val J)) :
    Function.Surjective π := by sorry
