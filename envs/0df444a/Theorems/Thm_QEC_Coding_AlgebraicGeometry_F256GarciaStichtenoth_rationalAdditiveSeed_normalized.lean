-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_rationalAdditiveSeed_normalized
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.rationalAdditiveSeed_normalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:34:24.941344+00:00
-- url     : https://prove2.me/theorems/bf5e06fd-a037-4c6d-97ff-79559654628f
-- title:
--   F256 Garcia Stichtenoth: rational Additive Seed normalized
-- statement:
--   The actual additive seed, with no different or trace-normalization
--   input: these follow from the literal rational generator `w`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/EmbeddedWSeed.lean#L37-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/EmbeddedWSeed.lean#L37-L57

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_EmbeddedSourceCoordinates
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalTraceSeed
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_EmbeddedWSeed
set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable {E : Type*} [_root_.Field E] [Algebra F256 E]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.rationalAdditiveSeed_normalized (Q : GlobalPlace F256 E) (w x : E)
    (hw : Transcendental F256 w) (hx : x ^ 16 + x = w)
    [FiniteDimensional F256⟮w⟯ E] [Algebra.IsSeparable F256⟮w⟯ E] :
    PlaceNormalizedExtension Q F256⟮w⟯ F256⟮x⟯ := by sorry
