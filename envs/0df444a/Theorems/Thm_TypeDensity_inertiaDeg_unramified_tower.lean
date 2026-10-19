-- Prove2me | Theorems.Thm_TypeDensity_inertiaDeg_unramified_tower
-- name    : TypeDensity.inertiaDeg_unramified_tower
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:31:57.207978+00:00
-- url     : https://prove2.me/theorems/eedccdd1-154b-4245-aebc-26e4c00d30ce
-- title:
--   In a tower `O → O_δ → B` with `O_δ` unramified of rank `δ` over `O`, inertia degrees over `O` are `δ` times inertia degrees over `O_δ`.
-- statement:
--   In a tower `O → O_δ → B` with `O_δ` unramified of rank `δ` over `O`, inertia degrees over `O` are `δ` times inertia degrees over `O_δ`.
-- source:
--   TypeDensity/Unramified/FrobeniusDescent.lean#L196-L210

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

theorem TypeDensity.inertiaDeg_unramified_tower (O Oδ B : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing Oδ] [IsDomain Oδ] [IsDiscreteValuationRing Oδ]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra O Oδ] [Algebra O B]
    [Algebra Oδ B] [IsScalarTower O Oδ B] [Module.Finite O Oδ] [Module.Free O Oδ]
    [Module.Finite Oδ B] (δ : ℕ) (hrank : Module.finrank O Oδ = δ) (pi : O)
    (hpi : Irreducible pi) (hpiδ : Irreducible (algebraMap O Oδ pi)) :
    (IsLocalRing.maximalIdeal B).inertiaDeg O =
      δ * (IsLocalRing.maximalIdeal B).inertiaDeg Oδ := by sorry
