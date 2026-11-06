-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_PolynomialMaximalPoints_complexPolynomialMaximal_exists_eval
-- name    : QEC.Coding.AlgebraicGeometry.PolynomialMaximalPoints.complexPolynomialMaximal_exists_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:11:49.106551+00:00
-- url     : https://prove2.me/theorems/54687e0a-a812-4993-abaf-3e72b5c0828f
-- title:
--   Polynomial Maximal Points: complex Polynomial Maximal exists eval
-- statement:
--   The Polynomial Maximal Points construction uses the complex Polynomial Maximal exists eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/PolynomialMaximalPoints.lean#L21-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/PolynomialMaximalPoints.lean#L21-L38

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_PolynomialMaximalPoints
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.PolynomialMaximalPoints
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.PolynomialMaximalPoints.complexPolynomialMaximal_exists_eval (M : Ideal (Polynomial ℂ))
    [M.IsMaximal] : ∃ a : ℂ, ∀ p : Polynomial ℂ, p ∈ M ↔ p.eval a = 0 := by sorry
