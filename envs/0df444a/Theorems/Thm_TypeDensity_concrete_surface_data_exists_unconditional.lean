-- Prove2me | Theorems.Thm_TypeDensity_concrete_surface_data_exists_unconditional
-- name    : TypeDensity.concrete_surface_data_exists_unconditional
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:00:27.464969+00:00
-- url     : https://prove2.me/theorems/70ae824e-453b-480d-ac21-7a18d39d0dd1
-- title:
--   The concrete surface is a regular local domain carrying `SurfaceData` with uniformizer `π`, parameters `t, x`, unit `u` and exponents `a, b`.
-- statement:
--   The concrete surface is a regular local domain carrying `SurfaceData` with uniformizer `π`, parameters `t, x`, unit `u` and exponents `a, b`.
-- source:
--   TypeDensity/Surfaces/Regularity.lean#L402-L414

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_concrete_surface_isAdicComplete_maximalIdeal
import Theorems.Thm_TypeDensity_concrete_surface_vertical
import Theorems.Thm_TypeDensity_concrete_surface_base_injective
import Theorems.Thm_TypeDensity_concrete_surface_maximalIdeal_eq
import Theorems.Thm_TypeDensity_concrete_surface_residueField_equiv
import Theorems.Thm_TypeDensity_concrete_surface_isDomain
import Theorems.Thm_TypeDensity_concrete_surface_isRegularLocalRing
import Theorems.Thm_TypeDensity_concrete_surface_ringKrullDim_eq_two
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
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.concrete_surface_data_exists_unconditional (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (pi : O)
    (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a) :
    ∃ (_ : IsDomain (ConcreteSurface O pi u a b))
      (_ : IsRegularLocalRing (ConcreteSurface O pi u a b)),
      ∃ D : SurfaceData O (ConcreteSurface O pi u a b),
      D.pi = pi ∧ D.t = surfaceT O pi u a b ∧ D.x = surfaceX O pi u a b ∧ D.unit =
      surfaceUnit O pi u a b ∧ D.a = a ∧ D.b = b := by sorry
