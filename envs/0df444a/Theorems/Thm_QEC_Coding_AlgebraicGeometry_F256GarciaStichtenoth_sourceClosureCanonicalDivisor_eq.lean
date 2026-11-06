-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureCanonicalDivisor_eq
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureCanonicalDivisor_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:32:31.833557+00:00
-- url     : https://prove2.me/theorems/5571dbb8-7ff3-4118-a0d1-49e9edec01b0
-- title:
--   F256 Garcia Stichtenoth: source Closure Canonical Divisor eq
-- statement:
--   The paper's displayed divisor identity, for the actual intrinsic
--   canonical divisor and the actual reduced fibres.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureCanonicalDifferential.lean#L82-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureCanonicalDifferential.lean#L82-L107

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureCanonicalDivisor_eq (m : ℕ) :
    sourceClosureCanonicalDivisor m =
      (16 * (sourceGaloisWZeroRamificationIndex m : ℤ) - 2) • sourceGaloisWZeroFibreDivisor m +
        ((sourceGaloisWInfinityRamificationIndex m : ℤ) - 2) •
          sourceGaloisWInfinityFibreDivisor m - sourceGaloisClosureSelectedDivisor m := by sorry
