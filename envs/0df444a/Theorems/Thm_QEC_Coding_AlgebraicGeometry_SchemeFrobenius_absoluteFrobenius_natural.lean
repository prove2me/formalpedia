-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_SchemeFrobenius_absoluteFrobenius_natural
-- name    : QEC.Coding.AlgebraicGeometry.SchemeFrobenius.absoluteFrobenius_natural
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:56:54.1442+00:00
-- url     : https://prove2.me/theorems/57773098-1bf4-4ed1-a1d2-9b4e907a7091
-- title:
--   Scheme Frobenius: absolute Frobenius natural
-- statement:
--   The Scheme Frobenius construction uses the absolute Frobenius natural property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/AbsoluteFrobenius.lean#L77-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/AbsoluteFrobenius.lean#L77-L98

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

theorem QEC.Coding.AlgebraicGeometry.SchemeFrobenius.absoluteFrobenius_natural {Y : Scheme} (g : X ⟶ Y)
    (h : Y ⟶ Spec (.of (ZMod p))) :
    absoluteFrobenius p X f ≫ g = g ≫ absoluteFrobenius p Y h := by sorry
