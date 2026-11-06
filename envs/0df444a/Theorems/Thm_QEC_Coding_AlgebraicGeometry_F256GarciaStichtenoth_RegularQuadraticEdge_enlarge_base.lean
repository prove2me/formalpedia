-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_RegularQuadraticEdge_enlarge_base
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.RegularQuadraticEdge.enlarge_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:12:12.716639+00:00
-- url     : https://prove2.me/theorems/a2d959b3-66c8-4fba-b972-5345b53cd6bf
-- title:
--   Regular Quadratic Edge: enlarge base
-- statement:
--   Enlarging the lower field retains the same literal regular generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularRefinement.lean#L31-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularRefinement.lean#L31-L36

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_TraceRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularRefinement
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {F E : Type*} [_root_.Field F] [_root_.Field E] [Algebra F E]
  [Algebra F256 E] (Q : GlobalPlace F256 E)

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.RegularQuadraticEdge.enlarge_base {K L M : IntermediateField F E}
    (h : RegularQuadraticEdge Q K L) (hKM : K ≤ M) :
    RegularQuadraticEdge Q M (M ⊔ L) := by sorry
