-- Prove2me | Theorems.Thm_TypeDensity_wf_returnWeight
-- name    : TypeDensity.wf_returnWeight
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:02:21.438003+00:00
-- url     : https://prove2.me/theorems/4d28abd0-e87f-4b2d-b01a-474c3a7eca80
-- title:
--   The return weights are well formed.
-- statement:
--   The return weights are well formed.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L729-L731

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_Expr_wf_pow
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

theorem TypeDensity.wf_returnWeight (c : ℕ) : (returnWeight c).wf := by sorry
