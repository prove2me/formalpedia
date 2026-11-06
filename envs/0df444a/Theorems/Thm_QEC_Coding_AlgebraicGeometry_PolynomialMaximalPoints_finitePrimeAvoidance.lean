-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_PolynomialMaximalPoints_finitePrimeAvoidance
-- name    : QEC.Coding.AlgebraicGeometry.PolynomialMaximalPoints.finitePrimeAvoidance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:11:56.5539+00:00
-- url     : https://prove2.me/theorems/2ebaf1ad-f892-457d-aeea-ac9178a2db24
-- title:
--   Polynomial Maximal Points: finite Prime Avoidance
-- statement:
--   The Polynomial Maximal Points construction uses the finite Prime Avoidance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/PolynomialMaximalPoints.lean#L46-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/PolynomialMaximalPoints.lean#L46-L57

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_PolynomialMaximalPoints
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.PolynomialMaximalPoints
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.PolynomialMaximalPoints.finitePrimeAvoidance {R : Type*} [CommRing R] [Nontrivial R]
    (M : Ideal R) [M.IsMaximal] (S : Set (Ideal R)) (hS : S.Finite)
    (hprime : ∀ I ∈ S, I.IsPrime) (houtside : M ∉ S) :
    ∃ g ∈ M, ∀ I ∈ S, g ∉ I := by sorry
