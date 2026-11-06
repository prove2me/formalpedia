-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureCanonicalDivisor_isCanonical
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureCanonicalDivisor_isCanonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:32:36.923353+00:00
-- url     : https://prove2.me/theorems/9e6d5eae-48e8-44ee-8778-f098a9d2b31b
-- title:
--   F256 Garcia Stichtenoth: source Closure Canonical Divisor is Canonical
-- statement:
--   The F256 Garcia Stichtenoth construction uses the source Closure Canonical Divisor is Canonical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureCanonicalDifferential.lean#L75-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureCanonicalDifferential.lean#L75-L78

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferentialDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSelectedDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureCanonicalDifferential
set_option autoImplicit false
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.canonicalDifferentialModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.canonicalDifferentialSMul
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureCanonicalDivisor_isCanonical (m : ℕ) :
    IsCanonicalDivisor (k := F256) (F := SourceGaloisClosureField m)
      (sourceClosureCanonicalDivisor m) := by sorry
