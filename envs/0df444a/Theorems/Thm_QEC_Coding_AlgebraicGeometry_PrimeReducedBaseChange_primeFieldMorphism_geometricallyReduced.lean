-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_PrimeReducedBaseChange_primeFieldMorphism_geometricallyReduced
-- name    : QEC.Coding.AlgebraicGeometry.PrimeReducedBaseChange.primeFieldMorphism_geometricallyReduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:55:38.945317+00:00
-- url     : https://prove2.me/theorems/6b742945-9215-4aef-9d80-925f42ec2b8a
-- title:
--   Prime Reduced Base Change: prime Field Morphism geometrically Reduced
-- statement:
--   The Prime Reduced Base Change construction uses the prime Field Morphism geometrically Reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/PrimeReducedBaseChange.lean#L126-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/PrimeReducedBaseChange.lean#L126-L133

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

theorem QEC.Coding.AlgebraicGeometry.PrimeReducedBaseChange.primeFieldMorphism_geometricallyReduced
    (p : ℕ) [Fact p.Prime] (X : Scheme)
    [_root_.AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Spec (.of (ZMod p))) : GeometricallyReduced f := by sorry
