-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_separable_extension_not_prime_power
-- name    : QEC.Coding.AlgebraicGeometry.separable_extension_not_prime_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:47:05.091196+00:00
-- url     : https://prove2.me/theorems/cb1544b6-53d6-4bb2-969a-1f1764e07cd2
-- title:
--   Algebraic Geometry: separable extension not prime power
-- statement:
--   A separable extension cannot create a missing p-th root in characteristic p.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeGaussNormality.lean#L139-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeGaussNormality.lean#L139-L153

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

theorem QEC.Coding.AlgebraicGeometry.separable_extension_not_prime_power
    (K E : Type*) [Field K] [Field E] [Algebra K E] [Algebra.IsSeparable K E]
    (p : ℕ) [ExpChar K p] (a : K) (ha : ∀ b : K, b^p ≠ a) (u : E) :
    u^p ≠ algebraMap K E a := by sorry
