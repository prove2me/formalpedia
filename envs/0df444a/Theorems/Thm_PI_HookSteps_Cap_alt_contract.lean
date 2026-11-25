-- Prove2me | Theorems.Thm_PI_HookSteps_Cap_alt_contract
-- name    : PI.HookSteps.Cap.alt_contract
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:07:44.644863+00:00
-- url     : https://prove2.me/theorems/e80f3666-59b5-5319-9707-7439acfd9c94
-- title:
--   Cap: alt contract
-- statement:
--   The Cap construction uses the alt contract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/CapelliMain.lean#L74-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/CapelliMain.lean#L74-L120

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

theorem PI.HookSteps.Cap.alt_contract {k : ℕ} (Q : (Fin k → I) → 𝒰) (r : Fin (k + 1) → I) (b : I) :
    ∑ σ : Equiv.Perm (Fin (k + 1)), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
      ((k : ℕ) • (if r (σ 0) = b then Q (fun i => r (σ i.succ)) else 0) +
        ∑ j : Fin k, if r (σ j.succ) = b then
          Q (Function.update (fun i => r (σ i.succ)) j (r (σ 0))) else 0) = 0 := by sorry
