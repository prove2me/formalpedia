-- Prove2me | Theorems.Thm_TypeDensity_residueSeries_ker
-- name    : TypeDensity.residueSeries_ker
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:46.53349+00:00
-- url     : https://prove2.me/theorems/fc6d0ab0-99d8-4357-b83d-90193d4e817a
-- title:
--   The kernel of coefficient reduction `O[[T,X]] → k[[T,X]]` is `(π)`.
-- statement:
--   The kernel of coefficient reduction `O[[T,X]] → k[[T,X]]` is `(π)`.
-- source:
--   TypeDensity/Surfaces/PowerSeries.lean#L255-L279

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
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
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.residueSeries_ker (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (pi : O)
    (hpi : Irreducible pi) :
    RingHom.ker (residueSeries O) = Ideal.span {(MvPowerSeries.C pi : TwoSeries O)} := by sorry
