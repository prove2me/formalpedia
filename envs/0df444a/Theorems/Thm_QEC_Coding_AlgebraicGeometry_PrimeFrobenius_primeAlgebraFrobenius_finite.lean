-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_PrimeFrobenius_primeAlgebraFrobenius_finite
-- name    : QEC.Coding.AlgebraicGeometry.PrimeFrobenius.primeAlgebraFrobenius_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:56:30.031125+00:00
-- url     : https://prove2.me/theorems/a193f509-3d91-4017-be79-ef453465b3c7
-- title:
--   Prime Frobenius: prime Algebra Frobenius finite
-- statement:
--   The Prime Frobenius construction uses the prime Algebra Frobenius finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/PrimeAlgebraFrobenius.lean#L53-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/PrimeAlgebraFrobenius.lean#L53-L61

import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeAlgebraFrobenius
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.PrimeFrobenius
noncomputable section
variable (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] [Algebra (ZMod p) R]

theorem QEC.Coding.AlgebraicGeometry.PrimeFrobenius.primeAlgebraFrobenius_finite [Algebra.FiniteType (ZMod p) R] :
    (primeAlgebraFrobenius p R).Finite := by sorry
