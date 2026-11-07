-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_ratFunc_prime_coordinate_quotient_finrank
-- name    : QEC.Coding.AlgebraicGeometry.ratFunc_prime_coordinate_quotient_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:46:56.704366+00:00
-- url     : https://prove2.me/theorems/4aae9ed7-d0dc-4657-9920-18ac186d9f55
-- title:
--   Algebraic Geometry: rat Func prime coordinate quotient finrank
-- statement:
--   The Algebraic Geometry construction uses the rat Func prime coordinate quotient finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeGaussNormality.lean#L66-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeGaussNormality.lean#L66-L73

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

theorem QEC.Coding.AlgebraicGeometry.ratFunc_prime_coordinate_quotient_finrank
    (K : Type*) [Field K] (p : ℕ) :
    Module.finrank (RatFunc K)
      (AdjoinRoot ((Polynomial.X : Polynomial (RatFunc K))^p - Polynomial.C RatFunc.X)) = p := by sorry
