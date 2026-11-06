-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_PrimeFrobenius_primeAlgebraFrobenius_comp_base
-- name    : QEC.Coding.AlgebraicGeometry.PrimeFrobenius.primeAlgebraFrobenius_comp_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:56:51.133033+00:00
-- url     : https://prove2.me/theorems/e82c5a6e-9415-4724-aa83-29f1bc1a8ea5
-- title:
--   Prime Frobenius: prime Algebra Frobenius comp base
-- statement:
--   The Prime Frobenius construction uses the prime Algebra Frobenius comp base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/PrimeAlgebraFrobenius.lean#L40-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/PrimeAlgebraFrobenius.lean#L40-L43

import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeAlgebraFrobenius
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.PrimeFrobenius
noncomputable section
variable (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] [Algebra (ZMod p) R]

theorem QEC.Coding.AlgebraicGeometry.PrimeFrobenius.primeAlgebraFrobenius_comp_base :
    (primeAlgebraFrobenius p R).comp (algebraMap (ZMod p) R) = algebraMap (ZMod p) R := by sorry
