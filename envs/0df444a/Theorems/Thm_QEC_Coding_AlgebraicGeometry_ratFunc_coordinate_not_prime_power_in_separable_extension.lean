-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_ratFunc_coordinate_not_prime_power_in_separable_extension
-- name    : QEC.Coding.AlgebraicGeometry.ratFunc_coordinate_not_prime_power_in_separable_extension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:47:07.762861+00:00
-- url     : https://prove2.me/theorems/776e0f61-19a0-428d-b73d-a2e79b9371f2
-- title:
--   Algebraic Geometry: rat Func coordinate not prime power in separable extension
-- statement:
--   The Algebraic Geometry construction uses the rat Func coordinate not prime power in separable extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeGaussNormality.lean#L155-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeGaussNormality.lean#L155-L161

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussLocalOrder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeKronecker
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.ratFunc_coordinate_not_prime_power_in_separable_extension
    (K E : Type*) [Field K] [Field E] [Algebra (RatFunc K) E]
    [Algebra.IsSeparable (RatFunc K) E]
    (p : ℕ) [ExpChar (RatFunc K) p] (hp : p.Prime) (u : E) :
    u^p ≠ algebraMap (RatFunc K) E RatFunc.X := by sorry
