-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureCanonicalDifferentialAtPlace_coe
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureCanonicalDifferentialAtPlace_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:32:18.32609+00:00
-- url     : https://prove2.me/theorems/f3233a47-8dff-492b-8bae-eff6d5387ee3
-- title:
--   F256 Garcia Stichtenoth: source Closure Canonical Differential At Place coe
-- statement:
--   The F256 Garcia Stichtenoth construction uses the source Closure Canonical Differential At Place coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureCanonicalDifferential.lean#L116-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureCanonicalDifferential.lean#L116-L119

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureCanonicalDifferentialAtPlace_coe (m : ℕ)
    (Q : GlobalPlace F256 (SourceGaloisClosureField m)) :
    (sourceClosureCanonicalDifferentialAtPlace m Q : Differential F256 (SourceGaloisClosureField m)) =
      sourceClosureCanonicalDifferential m := by sorry
