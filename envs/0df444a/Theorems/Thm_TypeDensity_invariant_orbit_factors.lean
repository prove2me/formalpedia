-- Prove2me | Theorems.Thm_TypeDensity_invariant_orbit_factors
-- name    : TypeDensity.invariant_orbit_factors
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:43.602055+00:00
-- url     : https://prove2.me/theorems/61b97ad8-2fc9-4215-8892-afa0426a6044
-- title:
--   The Frobenius orbit products of the irreducible factors of `F` descend to distinct monic irreducible polynomials over `Frac O` whose product is the conjugate product of `F`.
-- statement:
--   The Frobenius orbit products of the irreducible factors of `F` descend to distinct monic irreducible polynomials over `Frac O` whose product is the conjugate product of `F`.
-- source:
--   TypeDensity/Unramified/Extension.lean#L1064-L1146

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Theorems.Thm_TypeDensity_distinct_monic_irreducible_coprime
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
set_option autoImplicit false

open TypeDensity
open Polynomial IsLocalRing MeasureTheory

theorem TypeDensity.invariant_orbit_factors (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) [IsDomain (AdjoinRoot Φ)]
    (ι : BaseField O →+* BaseField (AdjoinRoot Φ))
    (τ : ℕ → (BaseField (AdjoinRoot Φ) ≃+* BaseField (AdjoinRoot Φ)))
    (hτ : ∀ (i : ℕ) (x : AdjoinRoot Φ), τ i
      (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)) x) = algebraMap (AdjoinRoot Φ)
      (BaseField (AdjoinRoot Φ)) (frobeniusIter O Φ i x))
    (hτι : ∀ (i : ℕ) (y : BaseField O), τ i (ι y) = ι y)
    (hτ0 : τ 0 = RingEquiv.refl (BaseField (AdjoinRoot Φ)))
    (hrec : ∀ i : ℕ, τ (i+1) = (τ i).trans (τ 1))
    (hτδ : ∀ z : BaseField (AdjoinRoot Φ), τ Φ.natDegree z = z)
    (hfix : ∀ z : BaseField (AdjoinRoot Φ), τ 1 z = z → ∃ y : BaseField O, ι y = z)
    (hinj : Function.Injective ι) (F : Polynomial (AdjoinRoot Φ))
    (gs : List (Polynomial (BaseField (AdjoinRoot Φ)))) (hgs : ∀ g ∈ gs, g.Monic ∧ Irreducible g)
    (hd : gs.Pairwise (fun g h => g ≠ h))
    (hprod : F.map (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ))) = gs.prod)
    (hcop : ∀ i j : Fin Φ.natDegree, i ≠ j → IsCoprime
      ((fun i : Fin Φ.natDegree => (F.map (frobeniusIter O Φ i).toRingHom).map
          (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)))) i)
      ((fun i : Fin Φ.natDegree => (F.map (frobeniusIter O Φ i).toRingHom).map
          (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)))) j)) :
    ∃ H : Fin gs.length → Polynomial (BaseField O), (∀ a, (H a).Monic ∧ Irreducible (H a)) ∧
      Function.Injective H ∧
      (∀ a, (H a).map ι = ∏ i : Fin Φ.natDegree, (gs.get a).map (τ i).toRingHom) ∧
      (∀ a, (H a).natDegree = Φ.natDegree * (gs.get a).natDegree) ∧ (∏ a, H a).map ι =
      (conjugateProduct O Φ F).map (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ))) := by sorry
