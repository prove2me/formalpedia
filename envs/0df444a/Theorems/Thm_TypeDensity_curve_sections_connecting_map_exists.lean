-- Prove2me | Theorems.Thm_TypeDensity_curve_sections_connecting_map_exists
-- name    : TypeDensity.curve_sections_connecting_map_exists
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:15:08.419285+00:00
-- url     : https://prove2.me/theorems/5bb7ce8a-8cdd-4fab-8ed1-9fa13fbe5a52
-- title:
--   The connecting map from curve sections to the Čech cokernel exists, is surjective, and has kernel the image of the surface.
-- statement:
--   The connecting map from curve sections to the Čech cokernel exists, is surjective, and has kernel the image of the surface.
-- source:
--   TypeDensity/Recursion/Members.lean#L1391-L1423

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
import Definitions.Def_TypeDensity_Blowup_TwoChartCurveData
import Definitions.Def_TypeDensity_Surfaces_ConcreteAtlas
import Definitions.Def_TypeDensity_Recursion_Members
import Theorems.Thm_TypeDensity_curve_ideal_lattice_le_sections
import Theorems.Thm_TypeDensity_curve_sections_cover_overlap
import Theorems.Thm_TypeDensity_curve_section_connecting_class_zero_iff
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
open IsLocalRing MeasureTheory
open scoped BigOperators ENNReal

theorem TypeDensity.curve_sections_connecting_map_exists (O R : Type) [CommRing O] [CommRing R] [Algebra O R]
    (t x : R) (hreg : RegularParameterPair R t x) (beta : BlowupRestriction R t x)
    (hregSwap : RegularParameterPair R x t) (d : ℕ) (G : GluedGenerators R t x beta d) (j : ℕ)
    (h : cechInputLattice R t x j ≤ (cechOutputLattice R t x j).comap
    (fullCechDifferential R t x beta d)) (hregF : Function.Injective
    (fun c : BlowupOverlap R t x ⧸ (Ideal.span {overlapException R t x})^j => Ideal.Quotient.mk
    ((Ideal.span {overlapException R t x})^j) ((algebraMap (BlowupChart R t x)
    (BlowupOverlap R t x)) (G.left j)) * c)) :
    ∃ δ : curveSectionsQuot R t x beta G j →ₗ[O] (CechLevelOutput R t x j ⧸ LinearMap.range
      (finiteCechDifferential R t x beta d j h)), (∀ (p : BlowupChart R t x × BlowupChart R x t)
      (hp : p ∈ curveSections R t x beta G j) (c : BlowupOverlap R t x), fullCechDifferential R t x
      beta 0 p - (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (G.left j) * c ∈
      (Ideal.span {overlapException R t x})^j → δ ⟨(curveIdealLattice R t x beta G j).mkQ p,
      Submodule.mem_map_of_mem hp⟩ = (LinearMap.range (finiteCechDifferential R t x beta d j h)).mkQ
      ((cechOutputLattice R t x j).mkQ c)) ∧ Function.Surjective δ ∧ ∀ u : curveSectionsQuot R t x
      beta G j, δ u = 0 ↔ ∃ r : R, (u : (BlowupChart R t x × BlowupChart R x t) ⧸ curveIdealLattice
      R t x beta G j) = (curveIdealLattice R t x beta G j).mkQ (surfaceToChartPair R t x r) := by sorry
