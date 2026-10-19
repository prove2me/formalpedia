-- Prove2me | Theorems.Thm_TypeDensity_factor_invariant_algEquiv
-- name    : TypeDensity.factor_invariant_algEquiv
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:34:01.881703+00:00
-- url     : https://prove2.me/theorems/f4ae2913-1163-4e71-afbf-28271ea01df8
-- title:
--   `K`-isomorphic root fields of monic irreducibles `g, g'` (with finite closure) have the same factor invariant.
-- statement:
--   `K`-isomorphic root fields of monic irreducibles `g, g'` (with finite closure) have the same factor invariant.
-- source:
--   TypeDensity/Algebra/FactorInvariant.lean#L56-L69

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_field_invariant_algEquiv
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

theorem TypeDensity.factor_invariant_algEquiv (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (g g' : Polynomial (BaseField O)) (hg : g.Monic)
    (hirr : Irreducible g) (hg' : g'.Monic) (hirr' : Irreducible g')
    (e : AdjoinRoot g ≃ₐ[BaseField O] AdjoinRoot g')
    (hfin : Module.Finite O (integralClosure O (AdjoinRoot g))) :
    factorInvariant O g = factorInvariant O g' := by sorry
