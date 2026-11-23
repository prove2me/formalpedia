-- Prove2me | Theorems.Thm_PI_WSF_cr_rowAct_C
-- name    : PI.WSF.cr_rowAct_C
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:34.51388+00:00
-- url     : https://prove2.me/theorems/43ebc451-c080-4619-910e-a05b0500f1df
-- title:
--   WSF: cr row Act C
-- statement:
--   The WSF construction uses the cr row Act C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/CrRowActRowAct.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/CrRowActRowAct.lean#L15-L17

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

theorem PI.WSF.cr_rowAct_C {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (a : ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ g (C a : MvPolynomial (Fin N × Fin N) ℂ) = C a := by sorry
