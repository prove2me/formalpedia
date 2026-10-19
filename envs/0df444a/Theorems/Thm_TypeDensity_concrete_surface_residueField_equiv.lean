-- Prove2me | Theorems.Thm_TypeDensity_concrete_surface_residueField_equiv
-- name    : TypeDensity.concrete_surface_residueField_equiv
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:16.310458+00:00
-- url     : https://prove2.me/theorems/40056b9e-e522-4757-bf70-e0c0bd6c6685
-- title:
--   The residue field of the concrete surface is that of `O`, compatibly with `O → R`.
-- statement:
--   The residue field of the concrete surface is that of `O`, compatibly with `O → R`.
-- source:
--   TypeDensity/Surfaces/PowerSeries.lean#L967-L980

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Theorems.Thm_TypeDensity_concrete_surface_quotient_parameters_equiv
import Theorems.Thm_TypeDensity_concrete_surface_maximalIdeal_eq
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

theorem TypeDensity.concrete_surface_residueField_equiv (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) [IsLocalRing (ConcreteSurface O pi u a b)] :
    ∃ e : IsLocalRing.ResidueField O ≃+*
    IsLocalRing.ResidueField (ConcreteSurface O pi u a b), ∀ c : O, e (IsLocalRing.residue O c) =
    IsLocalRing.residue (ConcreteSurface O pi u a b)
    (algebraMap O (ConcreteSurface O pi u a b) c) := by sorry
