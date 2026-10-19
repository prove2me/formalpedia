-- Prove2me | Theorems.Thm_TypeDensity_curve_section_connecting_class_zero_iff
-- name    : TypeDensity.curve_section_connecting_class_zero_iff
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:00:21.024125+00:00
-- url     : https://prove2.me/theorems/3afd8aac-f623-415c-9551-f60e26684539
-- title:
--   The connecting class of a curve section vanishes iff the section differs from the image of a surface function by an element of the curve ideal lattice.
-- statement:
--   The connecting class of a curve section vanishes iff the section differs from the image of a surface function by an element of the curve ideal lattice.
-- source:
--   TypeDensity/Blowup/H0Comparison.lean#L796-L882

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
import Theorems.Thm_TypeDensity_surface_to_cech_range
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
open scoped BigOperators ENNReal

theorem TypeDensity.curve_section_connecting_class_zero_iff (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d : ℕ) (G : GluedGenerators R t x beta d)
    (hreg : RegularParameterPair R t x) (hregSwap : RegularParameterPair R x t) (j : ℕ)
    (h : cechInputLattice R t x j ≤ (cechOutputLattice R t x j).comap
    (fullCechDifferential R t x beta d))
    (hregF : Function.Injective
    (fun c : BlowupOverlap R t x ⧸ (Ideal.span {overlapException R t x})^j => Ideal.Quotient.mk
    ((Ideal.span {overlapException R t x})^j)
    ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (G.left j)) * c))
    (p : BlowupChart R t x × BlowupChart R x t) (hp : p ∈ curveSections R t x beta G j)
    (c : BlowupOverlap R t x)
    (hc : fullCechDifferential R t x beta 0 p -
    (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (G.left j) * c ∈
    (Ideal.span {overlapException R t x})^j) :
    (LinearMap.range (finiteCechDifferential R t x beta d j h)).mkQ
      ((cechOutputLattice R t x j).mkQ c) = 0 ↔ ∃ r : R, p - surfaceToChartPair R t x r ∈
      curveIdealLattice R t x beta G j := by sorry
