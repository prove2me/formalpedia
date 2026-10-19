-- Prove2me | Theorems.Thm_TypeDensity_surface_to_curve_quotient_kernel
-- name    : TypeDensity.surface_to_curve_quotient_kernel
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:00:43.306046+00:00
-- url     : https://prove2.me/theorems/0e7b138e-6681-41c7-a9e4-fa04ef966295
-- title:
--   A surface function `r` lies in the level-`j` curve lattice of the glued generators `G` iff `r ∈ (f) + (t, x)^j`, where `f` is a surface function inducing `G` at every level.
-- statement:
--   A surface function `r` lies in the level-`j` curve lattice of the glued generators `G` iff `r ∈ (f) + (t, x)^j`, where `f` is a surface function inducing `G` at every level.
-- source:
--   TypeDensity/Blowup/CurveSections.lean#L101-L186

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
import Theorems.Thm_TypeDensity_glued_function_left_chart
import Theorems.Thm_TypeDensity_glued_function_right_chart
import Theorems.Thm_TypeDensity_beta_right_chartBase_self
import Theorems.Thm_TypeDensity_surface_to_cech_kernel
import Theorems.Thm_TypeDensity_twisted_kernel_from_surface
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

theorem TypeDensity.surface_to_curve_quotient_kernel (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d : ℕ) (G : GluedGenerators R t x beta d)
    (hreg : RegularParameterPair R t x) (hregSwap : RegularParameterPair R x t) (j : ℕ)
    (hregF : Function.Injective (fun c : BlowupOverlap R t x ⧸
      (Ideal.span {overlapException R t x})^j =>
      Ideal.Quotient.mk ((Ideal.span {overlapException R t x})^j)
      ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (G.left j)) * c))
    (f : R)
    (hf : ∀ j : ℕ, surfaceToCechInput R t x j f =
      (cechInputLattice R t x j).mkQ (gluedFunctionPair R t x G j))
    (r : R) :
    surfaceToChartPair R t x r ∈ curveIdealLattice R t x beta G j ↔ r ∈ Ideal.span {f} ⊔
      (Ideal.span {t,x})^j := by sorry
