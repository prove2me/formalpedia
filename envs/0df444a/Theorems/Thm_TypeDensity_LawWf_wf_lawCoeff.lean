-- Prove2me | Theorems.Thm_TypeDensity_LawWf_wf_lawCoeff
-- name    : TypeDensity.LawWf.wf_lawCoeff
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:57.214329+00:00
-- url     : https://prove2.me/theorems/e823814a-7ca3-4e1c-9247-fccb20a561a3
-- title:
--   The `σ`-coefficient of a well-formed law is well formed.
-- statement:
--   The `σ`-coefficient of a well-formed law is well formed.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L1025-L1032

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
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

theorem TypeDensity.LawWf.wf_lawCoeff {L : Law} (h : LawWf L) (σ : FactorType) : (lawCoeff L σ).wf := by sorry
