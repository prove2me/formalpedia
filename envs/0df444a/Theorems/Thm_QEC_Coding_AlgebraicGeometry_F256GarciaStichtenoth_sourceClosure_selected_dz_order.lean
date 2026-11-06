-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosure_selected_dz_order
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosure_selected_dz_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:36:07.302201+00:00
-- url     : https://prove2.me/theorems/460b22c8-b193-4b97-98f0-20451e9c3fd8
-- title:
--   F256 Garcia Stichtenoth: source Closure selected dz order
-- statement:
--   The F256 Garcia Stichtenoth construction uses the source Closure selected dz order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SelectedFibreSeparation.lean#L18-L29
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SelectedFibreSeparation.lean#L18-L29

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureCanonicalDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedFibreSeparation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero

set_option autoImplicit false
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosure_selected_dz_order (m : ℕ)
    (j : Fin (sourceGaloisClosureSelectedLength m)) :
    differentialOrder (sourceGaloisClosureSelectedRationalPlace m j).place
      (functionFieldDifferentialGenerator (k := F256) (F := SourceGaloisClosureField m))
      functionFieldDifferentialGenerator_ne_zero = 0 := by sorry
