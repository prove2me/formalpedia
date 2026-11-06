-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceRecursion_fieldRange_sup_coordinate
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceRecursion_fieldRange_sup_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:35:00.294849+00:00
-- url     : https://prove2.me/theorems/090f4b5d-8114-4d31-9d82-09f33fc1e8e4
-- title:
--   F256 Garcia Stichtenoth: source Recursion field Range sup coordinate
-- statement:
--   The F256 Garcia Stichtenoth construction uses the source Recursion field Range sup coordinate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceCoordinates.lean#L102-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceCoordinates.lean#L102-L121

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalCoordinateCells
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceCoordinates
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceRecursion_fieldRange_sup_coordinate (m : ℕ) :
    (sourceRecursionEmbedding m).fieldRange ⊔ F256⟮sourceDistinguishedCoordinate (m + 1)⟯ =
      (⊤ : IntermediateField F256 (SourceField (m + 1))) := by sorry
