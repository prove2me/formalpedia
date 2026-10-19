-- Prove2me | Theorems.Thm_TypeDensity_unramified_free_module
-- name    : TypeDensity.unramified_free_module
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:10.447468+00:00
-- url     : https://prove2.me/theorems/6a305a2e-d942-4693-b704-67292b77dbf3
-- title:
--   For monic `Φ`, `O[X]/(Φ)` is a free `O`-module of finite rank `deg Φ`.
-- statement:
--   For monic `Φ`, `O[X]/(Φ)` is a free `O`-module of finite rank `deg Φ`.
-- source:
--   TypeDensity/Unramified/FrobeniusDescent.lean#L275-L280

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
open scoped BigOperators ENNReal

theorem TypeDensity.unramified_free_module (O : Type) [CommRing O] [Nontrivial O] (Φ : Polynomial O)
    (hΦ : Φ.Monic) :
    Module.Free O (AdjoinRoot Φ) ∧ Module.Finite O (AdjoinRoot Φ) ∧
      Module.finrank O (AdjoinRoot Φ) = Φ.natDegree := by sorry
