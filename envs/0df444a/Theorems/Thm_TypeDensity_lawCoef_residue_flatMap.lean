-- Prove2me | Theorems.Thm_TypeDensity_lawCoef_residue_flatMap
-- name    : TypeDensity.lawCoef_residue_flatMap
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:15:23.673846+00:00
-- url     : https://prove2.me/theorems/a93b25cc-9ea5-4384-959b-41d65af81d28
-- title:
--   lawCoef residue flatMap
-- statement:
--   The element of `Coef` of the law obtained by summing, over the residue patterns `m` of weight `n`, the divisor count of `m` (offset `1` or `0` according to `b`) times the product of the descended laws of the children of `m`, equals the pattern sum `patternSum ε 1 n n` with the same offset `ε`.
-- source:
--   TypeDensity/Reciprocity/Patterns.lean#L349-L359

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_lawCoef_otherChildren
import Theorems.Thm_TypeDensity_lawCoef_lawScale
import Theorems.Thm_TypeDensity_lawCoef_flatMap
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

theorem TypeDensity.lawCoef_residue_flatMap (n : ℕ) (b : Bool) :
    lawCoef ((residuePatterns n).toList.flatMap fun m ↦
      lawScale (divisorCount (if b then 1 else 0) m)
        (lawProd ((otherChildren 1 m).map fun z ↦ lawDescend z.1 (stateLaw z.2))))
      = patternSum (if b then 1 else 0) 1 n n := by sorry
