-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_RegularRefinement_finset_sup
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.RegularRefinement.finset_sup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:17:51.032437+00:00
-- url     : https://prove2.me/theorems/6c44fbd6-d52c-4791-9d3c-19be597a7e01
-- title:
--   Regular Refinement: finset sup
-- statement:
--   The Regular Refinement construction uses the finset sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularRefinement.lean#L58-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularRefinement.lean#L58-L70

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_TraceRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularRefinement
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {F E : Type*} [_root_.Field F] [_root_.Field E] [Algebra F E]
  [Algebra F256 E] (Q : GlobalPlace F256 E)

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.RegularRefinement.finset_sup {ι : Type*} (K : IntermediateField F E)
    (s : Finset ι) (L : ι → IntermediateField F E)
    (h : ∀ i ∈ s, RegularRefinement Q K (L i)) :
    RegularRefinement Q K (K ⊔ s.sup L) := by sorry
