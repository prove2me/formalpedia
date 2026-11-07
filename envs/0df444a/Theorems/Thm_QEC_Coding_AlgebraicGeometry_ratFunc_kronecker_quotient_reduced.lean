-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_ratFunc_kronecker_quotient_reduced
-- name    : QEC.Coding.AlgebraicGeometry.ratFunc_kronecker_quotient_reduced
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T04:47:09.302425+00:00
-- url     : https://prove2.me/theorems/2f979ffc-5399-4aba-8872-d3aef4221756
-- title:
--   Algebraic Geometry: rat Func kronecker quotient reduced
-- statement:
--   The Algebraic Geometry construction uses the rat Func kronecker quotient reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeGaussNormality.lean#L111-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeGaussNormality.lean#L111-L118

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

theorem QEC.Coding.AlgebraicGeometry.ratFunc_kronecker_quotient_reduced
    (K : Type*) [Field K] (p : ℕ) (hp : p.Prime) :
    IsReduced (AdjoinRoot (((Polynomial.X : Polynomial (RatFunc K)) -
      Polynomial.C ((RatFunc.X : RatFunc K)^p)) *
      ((Polynomial.X : Polynomial (RatFunc K))^p - Polynomial.C RatFunc.X))) := by sorry
