-- Prove2me | Theorems.Thm_PI_WSF_schurOrth_of
-- name    : PI.WSF.schurOrth_of
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:47:07.983643+00:00
-- url     : https://prove2.me/theorems/3c73342e-3bba-49a0-9e99-1ba8f6dee51d
-- title:
--   WSF: schur Orth of
-- statement:
--   The WSF construction uses the schur Orth of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/ConstructionC.lean#L45-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/ConstructionC.lean#L45-L214

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_InstMeasurableSpaceMat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_CzDiagUnitary
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_CiEvalMSmul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_CfEqSumOfSubset
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_ConstructionC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WSF
open Formalism.BasicNotions MvPolynomial MeasureTheory Matrix

theorem PI.WSF.schurOrth_of (h : PI.HwIrred) (hA : EvalOne) : SchurOrth := by sorry
