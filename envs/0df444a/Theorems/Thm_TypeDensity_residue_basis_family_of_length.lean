-- Prove2me | Theorems.Thm_TypeDensity_residue_basis_family_of_length
-- name    : TypeDensity.residue_basis_family_of_length
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:23.038578+00:00
-- url     : https://prove2.me/theorems/6e34c8b5-31c6-4553-a810-7e8e8c240a6b
-- title:
--   A module of length `N` killed by `π` has a residue basis family of size `N`.
-- statement:
--   A module of length `N` killed by `π` has a residue basis family of size `N`.
-- source:
--   TypeDensity/Surfaces/PowerSeries.lean#L565-L594

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

theorem TypeDensity.residue_basis_family_of_length (O B M : Type) [CommRing O] [CommRing B] [IsLocalRing B]
    [Algebra O B] [AddCommGroup M] [Module B M] [Module O M] [IsScalarTower O B M] (pi : O)
    (hsurj : ∀ b : B, ∃ c : O, b - algebraMap O B c ∈ IsLocalRing.maximalIdeal B)
    (hker : ∀ c : O, algebraMap O B c ∈ IsLocalRing.maximalIdeal B → pi ∣ c)
    (hpiM : ∀ m : M, pi • m = 0) (N : ℕ) (hN : Module.length B M = N) :
    ∃ β : Fin N → M, ResidueBasisFamily pi β := by sorry
