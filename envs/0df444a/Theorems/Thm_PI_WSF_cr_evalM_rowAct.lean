-- Prove2me | Theorems.Thm_PI_WSF_cr_evalM_rowAct
-- name    : PI.WSF.cr_evalM_rowAct
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:51:45.690832+00:00
-- url     : https://prove2.me/theorems/66adce1d-1e7e-4090-8134-8219ab6b1a1a
-- title:
--   WSF: cr eval M row Act
-- statement:
--   The WSF construction uses the cr eval M row Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/CrRowActRowAct.lean#L19-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/CrRowActRowAct.lean#L19-L32

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_InstMeasurableSpaceMat
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_CrRowActRowAct
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
open Formalism.BasicNotions MvPolynomial

theorem PI.WSF.cr_evalM_rowAct {N : ℕ} (g x : Matrix (Fin N) (Fin N) ℂ) (s : MvPolynomial (Fin N × Fin N) ℂ) :
    evalM x (Formalism.GradedWeylDivisibility.rowAct ℂ g s) = evalM (g * x) s := by sorry
