-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_SchemeFrobenius_sectionPower_apply
-- name    : QEC.Coding.AlgebraicGeometry.SchemeFrobenius.sectionPower_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:56:56.216239+00:00
-- url     : https://prove2.me/theorems/ec493e02-6b8c-4159-b750-51d35c611871
-- title:
--   Scheme Frobenius: section Power apply
-- statement:
--   The Scheme Frobenius construction uses the section Power apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/AbsoluteFrobenius.lean#L33-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/AbsoluteFrobenius.lean#L33-L34

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

theorem QEC.Coding.AlgebraicGeometry.SchemeFrobenius.sectionPower_apply (U : X.Opens) (s : Γ(X, U)) :
    sectionPower p X f U s = s^p := by sorry
