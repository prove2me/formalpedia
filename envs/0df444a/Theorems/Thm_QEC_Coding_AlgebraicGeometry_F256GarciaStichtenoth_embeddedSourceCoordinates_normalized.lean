-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_embeddedSourceCoordinates_normalized
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.embeddedSourceCoordinates_normalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:36:43.281302+00:00
-- url     : https://prove2.me/theorems/838a4990-06ba-457a-8958-0374cf4438f8
-- title:
--   F256 Garcia Stichtenoth: embedded Source Coordinates normalized
-- statement:
--   The whole source chain inside a finite ambient extension. It starts
--   at the actual image of `k(x₀)` and ends at the whole source field range.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/EmbeddedSourceCoordinates.lean#L79-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/EmbeddedSourceCoordinates.lean#L79-L98

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceCoordinates
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_EmbeddedSourceCoordinates
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable (m : ℕ) {E : Type*} [_root_.Field E] [Algebra F256 E]
    [Algebra (SourceField m) E] [IsScalarTower F256 (SourceField m) E]
    [FiniteDimensional (SourceField m) E] [Algebra.IsSeparable (SourceField m) E]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.embeddedSourceCoordinates_normalized
    (Q : GlobalPlace F256 E) [Finite Q.residueField] :
    PlaceNormalizedExtension Q
      F256⟮algebraMap (SourceField m) E (sourceCoordinates m 0)⟯
      (IsScalarTower.toAlgHom F256 (SourceField m) E).fieldRange := by sorry
