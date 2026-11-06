-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceBasicProjections_same_carrier
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceBasicProjections_same_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:21:46.943669+00:00
-- url     : https://prove2.me/theorems/27fe3c1f-be01-42c9-b77f-675c960ed8cc
-- title:
--   F256 Garcia Stichtenoth: source Basic Projections same carrier
-- statement:
--   The two Property-(A) projections have the same actual top subfield of
--   the source successor, despite their different choices of rational base.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BasicProjectionFields.lean#L235-L245
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BasicProjectionFields.lean#L235-L245

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_LiteralSourceStep
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalRecursionOrders
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionFields
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceBasicProjections_same_carrier (i : ℕ) :
    ((SourceBasicForwardField i)⟮sourceDistinguishedCoordinate (i + 1)⟯).restrictScalars F256 =
      ((SourceBasicReverseField i)⟮
        sourceRecursionEmbedding i ((sourceDistinguishedCoordinate i)⁻¹)⟯).restrictScalars F256 := by sorry
