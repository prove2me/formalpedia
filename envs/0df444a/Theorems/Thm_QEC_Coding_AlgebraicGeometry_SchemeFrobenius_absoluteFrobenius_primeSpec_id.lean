-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_SchemeFrobenius_absoluteFrobenius_primeSpec_id
-- name    : QEC.Coding.AlgebraicGeometry.SchemeFrobenius.absoluteFrobenius_primeSpec_id
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:56:56.322119+00:00
-- url     : https://prove2.me/theorems/16da0e70-a163-435f-b574-4364e1f84944
-- title:
--   Scheme Frobenius: absolute Frobenius prime Spec id
-- statement:
--   The Scheme Frobenius construction uses the absolute Frobenius prime Spec id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/AbsoluteFrobenius.lean#L100-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/AbsoluteFrobenius.lean#L100-L106

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

theorem QEC.Coding.AlgebraicGeometry.SchemeFrobenius.absoluteFrobenius_primeSpec_id :
    absoluteFrobenius p (Spec (.of (ZMod p))) (𝟙 _) = 𝟙 _ := by sorry
