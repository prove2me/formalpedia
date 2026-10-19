-- Prove2me | Theorems.Thm_TypeDensity_child_coordinate_map_scaled
-- name    : TypeDensity.child_coordinate_map_scaled
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:52.726116+00:00
-- url     : https://prove2.me/theorems/3bf9f923-faf0-4702-87f3-339eae6e4965
-- title:
--   The scaled strict map is `π` times the child coordinate map;
-- statement:
--   The scaled strict map is `π` times the child coordinate map; hence its range and preimages are those of the child coordinate map transported by `w ↦ π • w`.
-- source:
--   TypeDensity/Blowup/Charts.lean#L1071-L1092

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.child_coordinate_map_scaled (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (n : ℕ)
    (pi : O) (a : ℕ) (b : Fin n → R) (E : R ≃ₗ[O] ((Fin n → O) × R)) (H : (Fin n → O) →ₗ[O] R)
    (ha : 1 ≤ a) (hinj : Function.Injective (fun w : Fin n → O => pi • w)) :
    (∀ z : Fin n → O, pi • childCoordinateMap pi a b E H z = scaledStrictMap pi a b E H z) ∧
        Set.range (scaledStrictMap pi a b E H) = (fun w : Fin n → O => pi • w) '' Set.range
        (childCoordinateMap pi a b E H) ∧ ∀ T : Set (Fin n → O), scaledStrictMap pi a b E H ⁻¹'
        ((fun w : Fin n → O => pi • w) '' T) = childCoordinateMap pi a b E H ⁻¹' T := by sorry
