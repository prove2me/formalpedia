-- Prove2me | Theorems.Thm_PI_HookSteps_Cap_Pn_succ
-- name    : PI.HookSteps.Cap.Pn_succ
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:08:11.810035+00:00
-- url     : https://prove2.me/theorems/f3f3c840-e746-5086-a423-319c73fb3af2
-- title:
--   Cap: Pn succ
-- statement:
--   The Cap construction uses the Pn succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/CapelliMain.lean#L25-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/CapelliMain.lean#L25-L36

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

theorem PI.HookSteps.Cap.Pn_succ (x d : I → S → 𝒰) (hxx : ∀ a s b t, x a s * x b t = x b t * x a s)
    (hdx : ∀ a s b t, d b t * x a s = x a s * d b t + if a = b ∧ s = t then 1 else 0)
    {k : ℕ} (w g : Fin (k + 1) → I) :
    Pn x d w g = Eop x d (w 0) (g 0) * Pn x d (fun i => w i.succ) (fun i => g i.succ) -
      ∑ j : Fin k, if w j.succ = g 0 then
        Pn x d (Function.update (fun i => w i.succ) j (w 0)) (fun i => g i.succ) else 0 := by sorry
