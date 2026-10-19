-- Prove2me | Theorems.Thm_TypeDensity_pPow_pPow
-- name    : TypeDensity.pPow_pPow
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:52:59.173495+00:00
-- url     : https://prove2.me/theorems/d0ff3160-e808-4f73-bd92-3f6ebc25a174
-- title:
--   `P_w ∘ P_z = P_{wz}`.
-- statement:
--   `P_w ∘ P_z = P_{wz}`.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L452-L455

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_logSer_expSer
import Theorems.Thm_TypeDensity_scalar_mul
import Theorems.Thm_TypeDensity_moebiusSum_plethSum
import Theorems.Thm_TypeDensity_constantCoeff_plethSum
import Theorems.Thm_TypeDensity_constantCoeff_moebiusSum
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

theorem TypeDensity.pPow_pPow (w z : RatFunc ℚ) (g : Ser) : pPow w (pPow z g) = pPow (w * z) g := by sorry
