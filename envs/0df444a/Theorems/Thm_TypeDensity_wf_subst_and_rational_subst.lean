-- Prove2me | Theorems.Thm_TypeDensity_wf_subst_and_rational_subst
-- name    : TypeDensity.wf_subst_and_rational_subst
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:48.015783+00:00
-- url     : https://prove2.me/theorems/a05e3e05-6034-401f-8f20-dfff5fe14e6c
-- title:
--   Substituting a well-formed expression `e` for the variable, where `e.rational = φ(q)` for a ring endomorphism `φ` of `ℚ(q)`, preserves well-formedness and acts on rational functions as `φ` (the two fa
-- statement:
--   Substituting a well-formed expression `e` for the variable, where `e.rational = φ(q)` for a ring endomorphism `φ` of `ℚ(q)`, preserves well-formedness and acts on rational functions as `φ` (the two facts are proved by a joint induction).
-- source:
--   TypeDensity/Reciprocity/Patterns.lean#L172-L206

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_Expr_fraction_snd_ne_zero
import Theorems.Thm_TypeDensity_Expr_rational_add
import Theorems.Thm_TypeDensity_Expr_rational_mul
import Theorems.Thm_TypeDensity_Expr_rational_inv
import Theorems.Thm_TypeDensity_Expr_rational_const
import Theorems.Thm_TypeDensity_Expr_rational_var
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

theorem TypeDensity.wf_subst_and_rational_subst (e : Expr) (he : e.wf) (φ : RatFunc ℚ →+* RatFunc ℚ)
    (hX : e.rational = φ RatFunc.X) (x : Expr) (hx : x.wf) :
    (x.subst e).wf ∧ (x.subst e).rational = φ x.rational := by sorry
