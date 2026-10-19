-- Prove2me | Theorems.Thm_TypeDensity_pPow_mul_pPow
-- name    : TypeDensity.pPow_mul_pPow
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:20:08.723452+00:00
-- url     : https://prove2.me/theorems/1d808c80-7bca-48f4-a846-7663fb5b2dd4
-- title:
--   `P_w P_z = P_{w+z}`.
-- statement:
--   `P_w P_z = P_{w+z}`.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L457-L459

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_expSer_add
import Theorems.Thm_TypeDensity_scalar_add
import Theorems.Thm_TypeDensity_plethSum_add
import Theorems.Thm_TypeDensity_constantCoeff_plethSum
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

theorem TypeDensity.pPow_mul_pPow (w z : RatFunc ℚ) (g : Ser) : pPow w g * pPow z g = pPow (w + z) g := by sorry
