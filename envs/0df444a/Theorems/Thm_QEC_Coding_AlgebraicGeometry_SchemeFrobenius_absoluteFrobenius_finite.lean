-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_SchemeFrobenius_absoluteFrobenius_finite
-- name    : QEC.Coding.AlgebraicGeometry.SchemeFrobenius.absoluteFrobenius_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:57:29.330641+00:00
-- url     : https://prove2.me/theorems/b8fdf388-d7c2-4327-9e9e-0c2d581da7cd
-- title:
--   Scheme Frobenius: absolute Frobenius finite
-- statement:
--   The Scheme Frobenius construction uses the absolute Frobenius finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/AbsoluteFrobenius.lean#L120-L128
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/AbsoluteFrobenius.lean#L120-L128

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeAlgebraFrobenius
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Geometry.RingedSpace.Stalks
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_AbsoluteFrobenius
set_option autoImplicit false
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.SchemeFrobenius
noncomputable section
open QEC.Coding.AlgebraicGeometry.PrimeFrobenius
variable (p : ℕ) [Fact p.Prime] (X : Scheme) (f : X ⟶ Spec (.of (ZMod p)))

theorem QEC.Coding.AlgebraicGeometry.SchemeFrobenius.absoluteFrobenius_finite [LocallyOfFiniteType f] :
    IsFinite (absoluteFrobenius p X f) := by sorry
