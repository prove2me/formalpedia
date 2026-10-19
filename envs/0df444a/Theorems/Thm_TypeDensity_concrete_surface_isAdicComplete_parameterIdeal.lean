-- Prove2me | Theorems.Thm_TypeDensity_concrete_surface_isAdicComplete_parameterIdeal
-- name    : TypeDensity.concrete_surface_isAdicComplete_parameterIdeal
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:55.561236+00:00
-- url     : https://prove2.me/theorems/50067f3e-2159-4a89-b5a2-d2577c63332d
-- title:
--   The concrete surface is complete for its parameter ideal `(t, x)`.
-- statement:
--   The concrete surface is complete for its parameter ideal `(t, x)`.
-- source:
--   TypeDensity/Surfaces/Completeness.lean#L318-L330

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_iInf_sup_pow_eq_of_isLocalRing
import Theorems.Thm_TypeDensity_isAdicComplete_quotient_of_iInf_sup_pow
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
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.TotallySplit
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.concrete_surface_isAdicComplete_parameterIdeal (O : Type) [CommRing O] [IsLocalRing O]
    [IsNoetherianRing O] (pi : O) (u : (TwoSeries O)ˣ) (a b : ℕ) :
    IsAdicComplete (surfaceParameterIdeal O pi u a b) (ConcreteSurface O pi u a b) := by sorry
