-- Prove2me | Theorems.Thm_TypeDensity_lawCoef_flatMap
-- name    : TypeDensity.lawCoef_flatMap
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:02:29.659345+00:00
-- url     : https://prove2.me/theorems/e1351667-531c-4797-9d48-6f9af432ebda
-- title:
--   `lawCoef` sends `flatMap` to the sum of the pieces.
-- statement:
--   `lawCoef` sends `flatMap` to the sum of the pieces.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L781-L784

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_lawInterp_flatMap
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
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Log
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.lawCoef_flatMap {α : Type} (xs : List α) (g : α → Law) :
    lawCoef (xs.flatMap g) = (xs.map fun u ↦ lawCoef (g u)).sum := by sorry
