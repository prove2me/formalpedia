-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_rationalGenerator_order_dichotomy
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.rationalGenerator_order_dichotomy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:35:00.040704+00:00
-- url     : https://prove2.me/theorems/de8c2157-95ee-42ff-a84e-75e52afc6852
-- title:
--   F256 Garcia Stichtenoth: rational Generator order dichotomy
-- statement:
--   A transcendental rational generator has only regular places and its
--   simple pole, with normalized order measured on the actual generated field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/EmbeddedWSeed.lean#L25-L33
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/EmbeddedWSeed.lean#L25-L33

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.rationalGenerator_order_dichotomy (w : E) (hw : Transcendental F256 w)
    (P : GlobalPlace F256 F256⟮w⟯) :
    P.order (AdjoinSimple.gen F256 w) = -1 ∨ 0 ≤ P.order (AdjoinSimple.gen F256 w) := by sorry
