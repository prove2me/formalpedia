-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_transportedStepAbovePlace_order_distinguishedCoordinate
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.transportedStepAbovePlace_order_distinguishedCoordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:09:01.045979+00:00
-- url     : https://prove2.me/theorems/4c3ca5e6-ce02-4add-ab49-29728a50924c
-- title:
--   F256 Garcia Stichtenoth: transported Step Above Place order distinguished Coordinate
-- statement:
--   The transported upper place makes the next distinguished coordinate a
--   normalized simple pole.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/StepPlaceTransport.lean#L60-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/StepPlaceTransport.lean#L60-L73

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Recursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_StepTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_StepPlaceTransport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
open QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.transportedStepAbovePlace_order_distinguishedCoordinate
    (i : ℕ) (P : GlobalPlace F256 (Field i))
    (hP : P.order (distinguishedCoordinate i) = -1) :
    (transportedStepAbovePlace i P hP).order
        (distinguishedCoordinate (i + 1)) = -1 := by sorry
