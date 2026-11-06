-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureWInfinityFibre_disjoint_selected
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureWInfinityFibre_disjoint_selected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:38:04.095202+00:00
-- url     : https://prove2.me/theorems/63d62893-3019-437d-8bbf-a560c11d32c8
-- title:
--   F256 Garcia Stichtenoth: source Closure WInfinity Fibre disjoint selected
-- statement:
--   The F256 Garcia Stichtenoth construction uses the source Closure WInfinity Fibre disjoint selected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SelectedFibreSeparation.lean#L53-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SelectedFibreSeparation.lean#L53-L73

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureCanonicalDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedFibreSeparation
set_option autoImplicit false
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureWInfinityFibre_disjoint_selected (m : ℕ) :
    Disjoint (sourceGaloisWInfinityFibreDivisor m).support
      (sourceGaloisClosureSelectedDivisor m).support := by sorry
