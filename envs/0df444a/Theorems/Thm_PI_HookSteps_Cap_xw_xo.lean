-- Prove2me | Theorems.Thm_PI_HookSteps_Cap_xw_xo
-- name    : PI.HookSteps.Cap.xw_xo
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:08:56.11308+00:00
-- url     : https://prove2.me/theorems/cb296ab6-0c36-49e9-9c69-f6a1daaf807a
-- title:
--   Cap: xw xo
-- statement:
--   The Cap construction uses the xw xo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/CapelliOps.lean#L56-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/CapelliOps.lean#L56-L68

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

theorem PI.HookSteps.Cap.xw_xo (N : ℕ) : ∀ (k : ℕ) (r s : Fin k → Fin N),
    xw (xo N) r s = Algebra.lmul ℚ (MvPolynomial (Fin N × Fin N) ℚ) (∏ j, X (r j, s j)) := by sorry
