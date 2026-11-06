-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureWZeroFibre_disjoint_selected
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureWZeroFibre_disjoint_selected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:35:34.284866+00:00
-- url     : https://prove2.me/theorems/b476870b-030d-46a5-96d8-e2d7dca2089c
-- title:
--   F256 Garcia Stichtenoth: source Closure WZero Fibre disjoint selected
-- statement:
--   The F256 Garcia Stichtenoth construction uses the source Closure WZero Fibre disjoint selected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SelectedFibreSeparation.lean#L31-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SelectedFibreSeparation.lean#L31-L51

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureCanonicalDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedFibreSeparation
set_option autoImplicit false
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureWZeroFibre_disjoint_selected (m : ℕ) :
    Disjoint (sourceGaloisWZeroFibreDivisor m).support
      (sourceGaloisClosureSelectedDivisor m).support := by sorry
