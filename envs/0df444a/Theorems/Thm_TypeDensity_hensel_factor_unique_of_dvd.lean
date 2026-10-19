-- Prove2me | Theorems.Thm_TypeDensity_hensel_factor_unique_of_dvd
-- name    : TypeDensity.hensel_factor_unique_of_dvd
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:03.27211+00:00
-- url     : https://prove2.me/theorems/9df39f73-4a67-4193-a8ef-ece48d4d2d76
-- title:
--   Over a local ring, a monic factorization `B C = B' C'` with `B ≡ B'` and `B̄, C̄` coprime is unique.
-- statement:
--   Over a local ring, a monic factorization `B C = B' C'` with `B ≡ B'` and `B̄, C̄` coprime is unique.
-- source:
--   TypeDensity/Unramified/Extension.lean#L955-L968

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Theorems.Thm_TypeDensity_hensel_pair_unique
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

theorem TypeDensity.hensel_factor_unique_of_dvd (O : Type) [CommRing O] [IsLocalRing O]
    (B C B' C' : Polynomial O) (hB : B.Monic) (hC : C.Monic) (hB' : B'.Monic) (hC' : C'.Monic)
    (hp : B * C = B' * C')
    (hred : B.map (IsLocalRing.residue O) = B'.map (IsLocalRing.residue O))
    (hc : IsCoprime (B.map (IsLocalRing.residue O)) (C.map (IsLocalRing.residue O))) :
    B = B' ∧ C = C' := by sorry
