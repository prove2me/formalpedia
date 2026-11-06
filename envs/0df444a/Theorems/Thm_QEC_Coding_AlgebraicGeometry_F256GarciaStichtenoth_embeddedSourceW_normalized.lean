-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_embeddedSourceW_normalized
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.embeddedSourceW_normalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:34:02.883423+00:00
-- url     : https://prove2.me/theorems/c96183c3-2ead-4436-b546-b4785c7356bf
-- title:
--   F256 Garcia Stichtenoth: embedded Source W normalized
-- statement:
--   The entire original source chain, rooted at its literal `k(w)` image
--   and ending at the whole source field range, at one fixed ambient place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/EmbeddedWSeed.lean#L115-L130
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/EmbeddedWSeed.lean#L115-L130

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_EmbeddedSourceCoordinates
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalTraceSeed
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_EmbeddedWSeed
set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable (m : ℕ) {E : Type*} [_root_.Field E] [Algebra F256 E]
    [Algebra (SourceField m) E] [IsScalarTower F256 (SourceField m) E]
    [FiniteDimensional (SourceField m) E] [Algebra.IsSeparable (SourceField m) E]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.embeddedSourceW_normalized (Q : GlobalPlace F256 E) [Finite Q.residueField] :
    PlaceNormalizedExtension Q F256⟮algebraMap (SourceField m) E
      (algebraMap (RatFunc F256) (SourceField m) galoisBaseW)⟯
      (IsScalarTower.toAlgHom F256 (SourceField m) E).fieldRange := by sorry
