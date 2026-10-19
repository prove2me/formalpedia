-- Prove2me | Theorems.Thm_TypeDensity_algebra_type_unique
-- name    : TypeDensity.algebra_type_unique
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:22.098571+00:00
-- url     : https://prove2.me/theorems/e19ebdae-7879-4867-99fc-4d20c5508ebc
-- title:
--   The algebra type of an `O`-algebra, if it exists, is unique.
-- statement:
--   The algebra type of an `O`-algebra, if it exists, is unique.
-- source:
--   TypeDensity/Algebra/FactorInvariant.lean#L230-L243

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_field_invariant_algEquiv
import Theorems.Thm_TypeDensity_pi_field_matching
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
open Polynomial

theorem TypeDensity.algebra_type_unique (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (B : Type) [CommRing B] [Algebra O B] (σ τ : FactorType) (hσ : HasAlgebraType O B σ)
    (hτ : HasAlgebraType O B τ) : σ = τ := by sorry
