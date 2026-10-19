-- Prove2me | Theorems.Thm_TypeDensity_concrete_surface_equiv_curve_length_and_regular
-- name    : TypeDensity.concrete_surface_equiv_curve_length_and_regular
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:58.020997+00:00
-- url     : https://prove2.me/theorems/4083f6b9-579c-40cd-88ef-a24956b74df7
-- title:
--   Transport of `powerSeries_quotient_length_eq_order` along an identification of the concrete surface modulo `t` with `k[[X]]`.
-- statement:
--   Along an identification of the concrete surface modulo `t` with `k⟦X⟧`, the length of `S/(g, t)` equals the order of the image of `g`, and multiplication by `g` is injective modulo `t` if and only if that image is nonzero.
-- source:
--   TypeDensity/Surfaces/PowerSeries.lean#L839-L895

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Theorems.Thm_TypeDensity_powerSeries_quotient_length_eq_order
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

theorem TypeDensity.concrete_surface_equiv_curve_length_and_regular (S : Type) [CommRing S] (O' : Type)
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] (pi' : O')
    (u' : (TwoSeries O')ˣ) (a' b' : ℕ) (Eq : S ≃+* ConcreteSurface O' pi' u' a' b')
    (q : (ConcreteSurface O' pi' u' a' b' ⧸ Ideal.span {surfaceT O' pi' u' a' b'}) ≃+*
      PowerSeries (IsLocalRing.ResidueField O')) (g : S) :
    Module.length S (S ⧸ Ideal.span {g, Eq.symm (surfaceT O' pi' u' a' b')}) =
    (q (Ideal.Quotient.mk (Ideal.span {surfaceT O' pi' u' a' b'}) (Eq g))).order ∧
    (Function.Injective
      (fun w : S ⧸ Ideal.span {Eq.symm (surfaceT O' pi' u' a' b')} ↦ Ideal.Quotient.mk
        (Ideal.span {Eq.symm (surfaceT O' pi' u' a' b')}) g * w) ↔
      q (Ideal.Quotient.mk (Ideal.span {surfaceT O' pi' u' a' b'}) (Eq g)) ≠ 0) := by sorry
