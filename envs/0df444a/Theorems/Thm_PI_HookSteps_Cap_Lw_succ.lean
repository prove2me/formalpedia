-- Prove2me | Theorems.Thm_PI_HookSteps_Cap_Lw_succ
-- name    : PI.HookSteps.Cap.Lw_succ
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:07:35.017523+00:00
-- url     : https://prove2.me/theorems/02a95981-782b-4585-9dc2-275d6e6bf110
-- title:
--   Cap: Lw succ
-- statement:
--   The Cap construction uses the Lw succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/CapelliMain.lean#L11-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/CapelliMain.lean#L11-L23

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliMain
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

theorem PI.HookSteps.Cap.Lw_succ (x d : I → S → 𝒰) {k : ℕ} (w g : Fin (k + 1) → I) :
    Lw x d w g = (Eop x d (w 0) (g 0) + if w 0 = g 0 then (k : 𝒰) else 0) *
      Lw x d (fun i => w i.succ) (fun i => g i.succ) := by sorry
