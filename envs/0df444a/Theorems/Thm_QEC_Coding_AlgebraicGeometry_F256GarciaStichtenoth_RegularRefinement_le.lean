-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_RegularRefinement_le
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.RegularRefinement.le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:12:01.942317+00:00
-- url     : https://prove2.me/theorems/435970d9-e3eb-4707-9339-14e6c7114063
-- title:
--   Regular Refinement: le
-- statement:
--   The Regular Refinement construction uses the le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularRefinement.lean#L42-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularRefinement.lean#L42-L46

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_TraceRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularRefinement
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {F E : Type*} [_root_.Field F] [_root_.Field E] [Algebra F E]
  [Algebra F256 E] (Q : GlobalPlace F256 E)

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.RegularRefinement.le {K L : IntermediateField F E}
    (h : RegularRefinement Q K L) : K ≤ L := by sorry
