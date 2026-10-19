-- Prove2me | Theorems.Thm_TypeDensity_reverse_normalized_irreducible
-- name    : TypeDensity.reverse_normalized_irreducible
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:01.851436+00:00
-- url     : https://prove2.me/theorems/404bf660-12f5-4e5d-b656-484dcc69ed88
-- title:
--   For a monic irreducible `g` with `g(0) ≠ 0` and finite closure, its normalized reversal `h = g(0)⁻¹ · reverse g` is monic irreducible of the same degree with `h(0) = g(0)⁻¹`, has the same factor invar
-- statement:
--   For a monic irreducible `g` with `g(0) ≠ 0` and finite closure, its normalized reversal `h = g(0)⁻¹ · reverse g` is monic irreducible of the same degree with `h(0) = g(0)⁻¹`, has the same factor invariant and finite closure, and normalized reversal of `h` gives back `g`.
-- source:
--   TypeDensity/Algebra/FactorInvariant.lean#L106-L168

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_integral_closure_algEquiv
import Theorems.Thm_TypeDensity_factor_invariant_algEquiv
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

theorem TypeDensity.reverse_normalized_irreducible (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (g : Polynomial (BaseField O)) (hg : g.Monic)
    (hgi : Irreducible g) (h0 : g.coeff 0 ≠ 0)
    (hfin : Module.Finite O (integralClosure O (AdjoinRoot g))) :
    (C (g.coeff 0)⁻¹ * g.reverse).Monic
      ∧ Irreducible (C (g.coeff 0)⁻¹ * g.reverse)
      ∧ (C (g.coeff 0)⁻¹ * g.reverse).natDegree = g.natDegree
      ∧ (C (g.coeff 0)⁻¹ * g.reverse).coeff 0 = (g.coeff 0)⁻¹
      ∧ factorInvariant O (C (g.coeff 0)⁻¹ * g.reverse) = factorInvariant O g
      ∧ C ((C (g.coeff 0)⁻¹ * g.reverse).coeff 0)⁻¹ * (C (g.coeff 0)⁻¹ * g.reverse).reverse =
        g
      ∧ Module.Finite O (integralClosure O (AdjoinRoot (C (g.coeff 0)⁻¹ * g.reverse))) := by sorry
