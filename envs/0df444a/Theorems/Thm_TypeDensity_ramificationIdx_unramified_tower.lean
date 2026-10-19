-- Prove2me | Theorems.Thm_TypeDensity_ramificationIdx_unramified_tower
-- name    : TypeDensity.ramificationIdx_unramified_tower
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:16.767029+00:00
-- url     : https://prove2.me/theorems/e97b34f7-5551-47a0-a1b3-29fe1f9ea8e7
-- title:
--   In a tower `O → O_δ → B` with `O_δ` unramified over `O`, ramification indices over `O` and over `O_δ` agree.
-- statement:
--   In a tower `O → O_δ → B` with `O_δ` unramified over `O`, ramification indices over `O` and over `O_δ` agree.
-- source:
--   TypeDensity/Unramified/FrobeniusDescent.lean#L212-L227

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_integral_local_extension_unique_prime
import Theorems.Thm_TypeDensity_unramified_base_invariants
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
import Mathlib.RingTheory.Henselian
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.ramificationIdx_unramified_tower (O Oδ B : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing Oδ] [IsDomain Oδ] [IsDiscreteValuationRing Oδ]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra O Oδ] [Algebra O B]
    [Algebra Oδ B] [IsScalarTower O Oδ B] [Module.Finite O Oδ] [Module.Free O Oδ]
    [Module.Finite Oδ B] (δ : ℕ) (hrank : Module.finrank O Oδ = δ) (pi : O)
    (hpi : Irreducible pi) (hpiδ : Irreducible (algebraMap O Oδ pi)) [Module.Free Oδ B] :
    (IsLocalRing.maximalIdeal B).ramificationIdx O =
      (IsLocalRing.maximalIdeal B).ramificationIdx Oδ := by sorry
