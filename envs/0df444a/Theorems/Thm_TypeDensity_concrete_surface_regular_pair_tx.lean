-- Prove2me | Theorems.Thm_TypeDensity_concrete_surface_regular_pair_tx
-- name    : TypeDensity.concrete_surface_regular_pair_tx
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:02.351982+00:00
-- url     : https://prove2.me/theorems/5dddb4e9-9b40-4869-ac68-74c9cb898adb
-- title:
--   `(t, x)` is a regular parameter pair of the concrete surface.
-- statement:
--   `(t, x)` is a regular parameter pair of the concrete surface.
-- source:
--   TypeDensity/Surfaces/Regularity.lean#L212-L220

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
import Theorems.Thm_TypeDensity_mvPowerSeries_quotient_var_regular
import Theorems.Thm_TypeDensity_mvPowerSeries_fin_two_quotient_var_regular_mod_var
import Theorems.Thm_TypeDensity_surfaceRelation_constantCoeff
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

theorem TypeDensity.concrete_surface_regular_pair_tx (O : Type) [CommRing O] [IsDomain O] (pi : O)
    (hpi : pi ≠ 0) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a) :
    RegularParameterPair (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b) := by sorry
