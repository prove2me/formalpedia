-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothGenus_fibre_identity
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothGenus_fibre_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:42:43.47768+00:00
-- url     : https://prove2.me/theorems/a5747610-5a25-4b5a-98cd-5da5146df4bd
-- title:
--   F256 Garcia Stichtenoth: f256 Garcia Stichtenoth Genus fibre identity
-- statement:
--   Denominator-free genus identity; the two subtracted terms are genuine
--   fibre degrees, not assumed bounds on a genus parameter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureDivisor.lean#L102-L115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureDivisor.lean#L102-L115

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ExplicitGarciaStichtenothTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureDivisor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothGenus_fibre_identity (i : ℕ) :
    15 * ((f256GarciaStichtenothGenus i : ℤ) - 1 +
      Divisor.degree GlobalPlace.residueDegree (f256GarciaStichtenothDivisorA i) +
      Divisor.degree GlobalPlace.residueDegree (f256GarciaStichtenothDivisorB i)) =
        f256GarciaStichtenothLength i := by sorry
