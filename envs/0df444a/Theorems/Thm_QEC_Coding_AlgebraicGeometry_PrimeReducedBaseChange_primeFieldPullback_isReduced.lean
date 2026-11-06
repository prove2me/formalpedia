-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_PrimeReducedBaseChange_primeFieldPullback_isReduced
-- name    : QEC.Coding.AlgebraicGeometry.PrimeReducedBaseChange.primeFieldPullback_isReduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:34:59.653001+00:00
-- url     : https://prove2.me/theorems/6903494e-db5b-415f-85d8-1776064abda5
-- title:
--   Prime Reduced Base Change: prime Field Pullback is Reduced
-- statement:
--   The Prime Reduced Base Change construction uses the prime Field Pullback is Reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/PrimeReducedBaseChange.lean#L94-L124
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/PrimeReducedBaseChange.lean#L94-L124

import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeAlgebraFrobenius
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeReducedBaseChange
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.PrimeReducedBaseChange
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem QEC.Coding.AlgebraicGeometry.PrimeReducedBaseChange.primeFieldPullback_isReduced
    (p : ℕ) [Fact p.Prime] (X : Scheme)
    [_root_.AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Spec (.of (ZMod p))) (K : Type) [Field K]
    (g : Spec (.of K) ⟶ Spec (.of (ZMod p))) :
    _root_.AlgebraicGeometry.IsReduced (pullback f g) := by sorry
