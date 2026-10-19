-- Prove2me | Theorems.Thm_TypeDensity_coeff_recipCoef_lawCoef
-- name    : TypeDensity.coeff_recipCoef_lawCoef
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:56.22228+00:00
-- url     : https://prove2.me/theorems/6b505a42-5000-42d1-96cb-a7930ac420ad
-- title:
--   For a well-formed law, the `σ`-coefficient of `lawCoef L` with `q ↦ 1/q` applied is the rational function of the coefficient expression with `q ↦ 1/q` substituted.
-- statement:
--   For a well-formed law, the `σ`-coefficient of `lawCoef L` with `q ↦ 1/q` applied is the rational function of the coefficient expression with `q ↦ 1/q` substituted.
-- source:
--   TypeDensity/Reciprocity/Patterns.lean#L222-L226

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_recipRat_X
import Theorems.Thm_TypeDensity_wf_subst_and_rational_subst
import Theorems.Thm_TypeDensity_Expr_rational_inv
import Theorems.Thm_TypeDensity_Expr_rational_var
import Theorems.Thm_TypeDensity_coeff_lawCoef
import Theorems.Thm_TypeDensity_LawWf_wf_lawCoeff
import Theorems.Thm_TypeDensity_recipCoef_coeff
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

theorem TypeDensity.coeff_recipCoef_lawCoef (L : Law) (hL : LawWf L) (σ : FactorType) :
    (recipCoef (lawCoef L)).coeff σ = ((lawCoeff L σ).subst (.inv .var)).rational := by sorry
