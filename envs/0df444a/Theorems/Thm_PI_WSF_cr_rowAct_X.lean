-- Prove2me | Theorems.Thm_PI_WSF_cr_rowAct_X
-- name    : PI.WSF.cr_rowAct_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:57:42.746904+00:00
-- url     : https://prove2.me/theorems/3b12859a-c8b0-476e-b88d-5b647ffc040f
-- title:
--   WSF: cr row Act X
-- statement:
--   The WSF construction uses the cr row Act X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/CrRowActRowAct.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/CrRowActRowAct.lean#L11-L13

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

theorem PI.WSF.cr_rowAct_X {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (w : Fin N × Fin N) :
    Formalism.GradedWeylDivisibility.rowAct ℂ g (X w : MvPolynomial (Fin N × Fin N) ℂ) = ∑ b : Fin N, C (g w.1 b) * X (b, w.2) := by sorry
