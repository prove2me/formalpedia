-- Prove2me | Theorems.Thm_TypeDensity_residue_extension_equiv
-- name    : TypeDensity.residue_extension_equiv
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:17.781983+00:00
-- url     : https://prove2.me/theorems/d4d984c2-0881-4a61-ac9c-2f50c13d0431
-- title:
--   The residue extension `O_δ / m_O O_δ` is isomorphic to `k[X]/(Φ̄)`, compatibly with reduction.
-- statement:
--   The residue extension `O_δ / m_O O_δ` is isomorphic to `k[X]/(Φ̄)`, compatibly with reduction.
-- source:
--   TypeDensity/Unramified/PolynomialTypes.lean#L946-L961

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
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
open scoped ENNReal

theorem TypeDensity.residue_extension_equiv (O : Type) [CommRing O] [IsLocalRing O] (Φ : Polynomial O) :
    ∃ e : residueExtension O Φ ≃+* AdjoinRoot (residuePoly O Φ),
      (∀ p : Polynomial O, e (baseReduce O Φ (AdjoinRoot.mk Φ p)) = AdjoinRoot.mk (residuePoly O Φ)
        (p.map (IsLocalRing.residue O))) ∧
      (∀ c : O, e (baseReduce O Φ (algebraMap O (AdjoinRoot Φ) c)) = algebraMap
        (IsLocalRing.ResidueField O) (AdjoinRoot (residuePoly O Φ)) (IsLocalRing.residue O c)) := by sorry
