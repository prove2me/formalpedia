-- Prove2me | Theorems.Thm_PI_HookSteps_Cap_dw_succ
-- name    : PI.HookSteps.Cap.dw_succ
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:08:57.095797+00:00
-- url     : https://prove2.me/theorems/a1a7c8cc-4203-54b2-88fe-1b4e31f10de2
-- title:
--   Cap: dw succ
-- statement:
--   The Cap construction uses the dw succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/CapelliAbs.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/CapelliAbs.lean#L16-L19

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliAbs
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
open Finset
variable {𝒰 : Type} [Ring 𝒰] {I S : Type} [DecidableEq I] [Fintype S] [DecidableEq S]

theorem PI.HookSteps.Cap.dw_succ (d : I → S → 𝒰) {k : ℕ} (g : Fin (k + 1) → I) (s : Fin (k + 1) → S) :
    dw d g s = d (g 0) (s 0) * dw d (fun i => g i.succ) (fun i => s i.succ) := by sorry
