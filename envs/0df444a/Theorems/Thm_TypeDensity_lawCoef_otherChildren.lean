-- Prove2me | Theorems.Thm_TypeDensity_lawCoef_otherChildren
-- name    : TypeDensity.lawCoef_otherChildren
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:00:36.913574+00:00
-- url     : https://prove2.me/theorems/2038a0fc-6c24-4312-843d-2ca1a02f8ddf
-- title:
--   The product of the descended laws of the off-boundary children of a pattern `m` is `Π_{(i,j)} ψ_{i+1}(F_{S(a;j+1)})^{m(i,j)}`.
-- statement:
--   The product of the descended laws of the off-boundary children of a pattern `m` is `Π_{(i,j)} ψ_{i+1}(F_{S(a;j+1)})^{m(i,j)}`.
-- source:
--   TypeDensity/Reciprocity/Patterns.lean#L240-L257

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_adamsRat_X
import Theorems.Thm_TypeDensity_lawWf_stateLaw
import Theorems.Thm_TypeDensity_wf_subst_and_rational_subst
import Theorems.Thm_TypeDensity_Expr_wf_pow
import Theorems.Thm_TypeDensity_Expr_rational_var
import Theorems.Thm_TypeDensity_lawCoef_lawProd
import Theorems.Thm_TypeDensity_Expr_rational_pow
import Theorems.Thm_TypeDensity_adamsCoef_single
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

theorem TypeDensity.lawCoef_otherChildren (a N : ℕ) (ha : 0 < a) (m : Pattern N) :
    lawCoef (lawProd ((otherChildren a m).map fun z ↦ lawDescend z.1 (stateLaw z.2))) =
        ∏ ij : Fin N × Fin N, (adamsCoef (ij.1.val + 1) (lawCoef
        (stateLaw (State.single a (ij.2.val + 1))))) ^ (m ij).val := by sorry
