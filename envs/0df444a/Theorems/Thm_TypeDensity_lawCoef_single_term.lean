-- Prove2me | Theorems.Thm_TypeDensity_lawCoef_single_term
-- name    : TypeDensity.lawCoef_single_term
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:14:55.335496+00:00
-- url     : https://prove2.me/theorems/4ddebef5-9a45-4891-bb9f-527b8ef1c7dc
-- title:
--   The contribution of an allowed tangent pattern `P` of `S(a;n)` to its recursion, as an element of `Coef`.
-- statement:
--   The contribution of an allowed tangent pattern `P` of `S(a;n)` to its recursion equals, in `Coef`, the scalar (divisor count × divisor probability) times the crossing-child law (if the tangent depth is positive) times the product of Adams operations applied to the single-child laws.
-- source:
--   TypeDensity/Reciprocity/Patterns.lean#L382-L406

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_children_valid
import Theorems.Thm_TypeDensity_adamsRat_X
import Theorems.Thm_TypeDensity_lawWf_stateLaw
import Theorems.Thm_TypeDensity_wf_subst_and_rational_subst
import Theorems.Thm_TypeDensity_lawCoef_otherChildren
import Theorems.Thm_TypeDensity_Expr_wf_pow
import Theorems.Thm_TypeDensity_Expr_rational_mul
import Theorems.Thm_TypeDensity_Expr_rational_var
import Theorems.Thm_TypeDensity_lawCoef_lawScale
import Theorems.Thm_TypeDensity_lawCoef_lawProd
import Theorems.Thm_TypeDensity_Expr_rational_pow
import Theorems.Thm_TypeDensity_adamsCoef_single
import Theorems.Thm_TypeDensity_adamsCoef_one
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

theorem TypeDensity.lawCoef_single_term (a n : ℕ) (ha : 0 < a) (hn : 0 < n)
    (P : TangentPattern (State.single a n).degree) (hP : Allowed (State.single a n) P) :
    lawCoef (lawScale (.mul (tangentCount (State.single a n) P)
        (divisorProbability (State.single a n) P.d.val))
        (lawProd ((children (State.single a n) P).map fun z ↦ lawDescend z.1 (stateLaw z.2)))) =
        scalar ((divisorCount 0 P.other).rational * (divisorProbability (State.single a n)
        P.d.val).rational) * ((if P.rt.val = 0 then 1 else lawCoef
        (stateLaw (State.crossing a a P.rt.val (n - P.d.val)))) *
        ∏ ij : Fin (State.single a n).degree × Fin (State.single a n).degree,
        (adamsCoef (ij.1.val + 1) (lawCoef (stateLaw (State.single a (ij.2.val + 1))))) ^
        (P.other ij).val) := by sorry
