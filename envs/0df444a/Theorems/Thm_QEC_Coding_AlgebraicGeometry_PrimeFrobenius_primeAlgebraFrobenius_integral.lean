-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_PrimeFrobenius_primeAlgebraFrobenius_integral
-- name    : QEC.Coding.AlgebraicGeometry.PrimeFrobenius.primeAlgebraFrobenius_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:07:51.619488+00:00
-- url     : https://prove2.me/theorems/69ba4dd2-7d8d-42ee-b6ba-1c090e922cde
-- title:
--   Prime Frobenius: prime Algebra Frobenius integral
-- statement:
--   The Prime Frobenius construction uses the prime Algebra Frobenius integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/PrimeAlgebraFrobenius.lean#L45-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/PrimeAlgebraFrobenius.lean#L45-L51

import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeAlgebraFrobenius
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.PrimeFrobenius
noncomputable section
variable (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] [Algebra (ZMod p) R]

theorem QEC.Coding.AlgebraicGeometry.PrimeFrobenius.primeAlgebraFrobenius_integral : (primeAlgebraFrobenius p R).IsIntegral := by sorry
