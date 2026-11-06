-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureCanonicalDivisor_degree
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureCanonicalDivisor_degree
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:34:55.540976+00:00
-- url     : https://prove2.me/theorems/0d497681-7e38-4eeb-82d5-f73491131bbf
-- title:
--   F256 Garcia Stichtenoth: source Closure Canonical Divisor degree
-- statement:
--   The F256 Garcia Stichtenoth construction uses the source Closure Canonical Divisor degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureGenus.lean#L39-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureGenus.lean#L39-L44

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureCanonicalDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureFullConstants
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Theorem
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureGenus
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureCanonicalDivisor_degree (m : ℕ) :
    Divisor.degree GlobalPlace.residueDegree (sourceClosureCanonicalDivisor m) =
      2 * (sourceClosureGenus m : ℤ) - 2 := by sorry
