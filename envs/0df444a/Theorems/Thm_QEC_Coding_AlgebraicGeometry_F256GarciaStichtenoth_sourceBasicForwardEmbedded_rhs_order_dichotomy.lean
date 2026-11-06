-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceBasicForwardEmbedded_rhs_order_dichotomy
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceBasicForwardEmbedded_rhs_order_dichotomy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:17:21.874951+00:00
-- url     : https://prove2.me/theorems/c1e17bf7-28e1-4dec-beb2-a05ae100d65a
-- title:
--   F256 Garcia Stichtenoth: source Basic Forward Embedded rhs order dichotomy
-- statement:
--   The F256 Garcia Stichtenoth construction uses the source Basic Forward Embedded rhs order dichotomy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BasicProjectionFields.lean#L44-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BasicProjectionFields.lean#L44-L61

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_LiteralSourceStep
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalRecursionOrders
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionFields
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceBasicForwardEmbedded_rhs_order_dichotomy
    (i : ℕ) (P : GlobalPlace F256 (SourceBasicForwardField i)) :
    P.order
        (sourceStepRhs
          (AdjoinSimple.gen F256
            (sourceRecursionEmbedding i (sourceDistinguishedCoordinate i)))) = -1 ∨
      0 ≤ P.order
        (sourceStepRhs
          (AdjoinSimple.gen F256
            (sourceRecursionEmbedding i (sourceDistinguishedCoordinate i)))) := by sorry
