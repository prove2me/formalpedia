-- Prove2me | Theorems.Thm_PI_HookSteps_Cap_mulLeft_eq_lmul
-- name    : PI.HookSteps.Cap.mulLeft_eq_lmul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:07:16.509827+00:00
-- url     : https://prove2.me/theorems/6cef5041-447a-51ef-81d9-91e2ebb5e7ad
-- title:
--   Cap: mul Left eq lmul
-- statement:
--   The Cap construction uses the mul Left eq lmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/CapelliOps.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/CapelliOps.lean#L9-L10

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliOps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.HookSteps PI.HookSteps.Cap
open MvPolynomial Finset

theorem PI.HookSteps.Cap.mulLeft_eq_lmul (N : ℕ) (p : MvPolynomial (Fin N × Fin N) ℚ) :
    LinearMap.mulLeft ℚ p = Algebra.lmul ℚ (MvPolynomial (Fin N × Fin N) ℚ) p := by sorry
