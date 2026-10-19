-- Prove2me | Theorems.Thm_TypeDensity_Expr_rational_inv
-- name    : TypeDensity.Expr.rational_inv
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:50.687346+00:00
-- url     : https://prove2.me/theorems/e53b28f2-49cb-4f10-a94a-512d77251c14
-- title:
--   `Expr.rational` commutes with inversion.
-- statement:
--   `Expr.rational` commutes with inversion.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L755-L758

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

theorem TypeDensity.Expr.rational_inv (x : Expr) : (Expr.inv x).rational = x.rational⁻¹ := by sorry
