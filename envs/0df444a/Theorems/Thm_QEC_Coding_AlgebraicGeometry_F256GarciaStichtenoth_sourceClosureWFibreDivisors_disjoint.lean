-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureWFibreDivisors_disjoint
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureWFibreDivisors_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:26:00.536034+00:00
-- url     : https://prove2.me/theorems/13f4aedc-5ad0-46a4-90b9-f2049be9f671
-- title:
--   F256 Garcia Stichtenoth: source Closure WFibre Divisors disjoint
-- statement:
--   The F256 Garcia Stichtenoth construction uses the source Closure WFibre Divisors disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureDifferentialDivisor.lean#L21-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureDifferentialDivisor.lean#L21-L43

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureFibreDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureRegularDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_CanonicalDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferentialDivisor
set_option autoImplicit false
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureWFibreDivisors_disjoint (m : ℕ) :
    Disjoint (sourceGaloisWZeroFibreDivisor m).support
      (sourceGaloisWInfinityFibreDivisor m).support := by sorry
