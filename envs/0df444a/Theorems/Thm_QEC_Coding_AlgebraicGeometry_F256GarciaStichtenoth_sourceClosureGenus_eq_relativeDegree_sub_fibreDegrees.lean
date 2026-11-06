-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureGenus_eq_relativeDegree_sub_fibreDegrees
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureGenus_eq_relativeDegree_sub_fibreDegrees
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:35:15.200227+00:00
-- url     : https://prove2.me/theorems/e802cf7a-e8d2-4dc3-a925-eff651f8f23d
-- title:
--   F256 Garcia Stichtenoth: source Closure Genus eq relative Degree sub fibre Degrees
-- statement:
--   Integer form of the source genus formula, derived from intrinsic
--   canonical degree and the actual two fibre degrees.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureGenus.lean#L48-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureGenus.lean#L48-L66

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureCanonicalDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureFullConstants
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Theorem
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureGenus
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureGenus_eq_relativeDegree_sub_fibreDegrees (m : ℕ) :
    (sourceClosureGenus m : ℤ) = 1 + (sourceGaloisWRelativeDegree m : ℤ) -
      Divisor.degree GlobalPlace.residueDegree (sourceGaloisWZeroFibreDivisor m) -
      Divisor.degree GlobalPlace.residueDegree (sourceGaloisWInfinityFibreDivisor m) := by sorry
