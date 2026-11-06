-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_PrimeFrobenius_primeAlgebraFrobenius_constant
-- name    : QEC.Coding.AlgebraicGeometry.PrimeFrobenius.primeAlgebraFrobenius_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:56:18.104947+00:00
-- url     : https://prove2.me/theorems/01b116e8-8dc1-4d3b-9b11-b832fe21bbda
-- title:
--   Prime Frobenius: prime Algebra Frobenius constant
-- statement:
--   The Prime Frobenius construction uses the prime Algebra Frobenius constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/PrimeAlgebraFrobenius.lean#L35-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/PrimeAlgebraFrobenius.lean#L35-L38

import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeAlgebraFrobenius
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.PrimeFrobenius
noncomputable section
variable (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] [Algebra (ZMod p) R]

theorem QEC.Coding.AlgebraicGeometry.PrimeFrobenius.primeAlgebraFrobenius_constant (a : ZMod p) :
    primeAlgebraFrobenius p R (algebraMap (ZMod p) R a) = algebraMap (ZMod p) R a := by sorry
