-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_PrimeReducedBaseChange_primeSpecPullback_isReduced
-- name    : QEC.Coding.AlgebraicGeometry.PrimeReducedBaseChange.primeSpecPullback_isReduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:34:31.045216+00:00
-- url     : https://prove2.me/theorems/e930fc46-975a-4c5c-90c2-7ca35afee351
-- title:
--   Prime Reduced Base Change: prime Spec Pullback is Reduced
-- statement:
--   The Prime Reduced Base Change construction uses the prime Spec Pullback is Reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/PrimeReducedBaseChange.lean#L82-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/PrimeReducedBaseChange.lean#L82-L92

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

theorem QEC.Coding.AlgebraicGeometry.PrimeReducedBaseChange.primeSpecPullback_isReduced
    (p : ℕ) [Fact p.Prime] (C K : Type) [CommRing C] [Field K]
    [_root_.IsReduced C]
    (f : Spec (.of C) ⟶ Spec (.of (ZMod p)))
    (g : Spec (.of K) ⟶ Spec (.of (ZMod p))) :
    _root_.AlgebraicGeometry.IsReduced (pullback f g) := by sorry
