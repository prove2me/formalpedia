-- Prove2me | Theorems.Thm_TypeDensity_concrete_surface_special_fiber_equiv
-- name    : TypeDensity.concrete_surface_special_fiber_equiv
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:47.345295+00:00
-- url     : https://prove2.me/theorems/87b7a325-9064-4ff9-9e63-d90a93dfeb04
-- title:
--   The special fiber of the concrete surface is `k[[T,X]]/(T^a X^b)`, compatibly with reduction of coefficients.
-- statement:
--   The special fiber of the concrete surface is `k[[T,X]]/(T^a X^b)`, compatibly with reduction of coefficients.
-- source:
--   TypeDensity/Surfaces/PowerSeries.lean#L794-L837

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Theorems.Thm_TypeDensity_residueSeries_ker
import Theorems.Thm_TypeDensity_residueSeries_surfaceRelation
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

theorem TypeDensity.concrete_surface_special_fiber_equiv (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) :
    ∃ e : (ConcreteSurface O pi u a b ⧸ Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})
    ≃+* SpecialFiber (IsLocalRing.ResidueField O) a b, ∀ s :
    TwoSeries O, e
    (Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})
      (surfaceMk O pi u a b s)) =
    Ideal.Quotient.mk (monomialIdeal (IsLocalRing.ResidueField O) a b) (residueSeries O s) := by sorry
