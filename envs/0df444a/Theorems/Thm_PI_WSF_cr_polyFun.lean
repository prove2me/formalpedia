-- Prove2me | Theorems.Thm_PI_WSF_cr_polyFun
-- name    : PI.WSF.cr_polyFun
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:45:41.234905+00:00
-- url     : https://prove2.me/theorems/0b4420a0-6604-4a99-bbac-c18c2287a1d2
-- title:
--   WSF: cr poly Fun
-- statement:
--   The WSF construction uses the cr poly Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/CrRowActRowAct.lean#L57-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/CrRowActRowAct.lean#L57-L85

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

theorem PI.WSF.cr_polyFun {N : ℕ} (s : MvPolynomial (Fin N × Fin N) ℂ) :
    ∀ L : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] ℂ, ∃ P : MvPolynomial (Fin N × Fin N) ℂ,
      ∀ g : Matrix (Fin N) (Fin N) ℂ, L (Formalism.GradedWeylDivisibility.rowAct ℂ g s) = evalM g P := by sorry
