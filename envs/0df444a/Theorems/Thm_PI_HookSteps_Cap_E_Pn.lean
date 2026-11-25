-- Prove2me | Theorems.Thm_PI_HookSteps_Cap_E_Pn
-- name    : PI.HookSteps.Cap.E_Pn
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:16:14.201351+00:00
-- url     : https://prove2.me/theorems/5606b11a-372c-5f7d-a8f2-e8180f5c84a1
-- title:
--   Cap: E Pn
-- statement:
--   The Cap construction uses the E Pn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/CapelliAbs.lean#L90-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/CapelliAbs.lean#L90-L124

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

theorem PI.HookSteps.Cap.E_Pn (x d : I → S → 𝒰) (hxx : ∀ a s b t, x a s * x b t = x b t * x a s)
    (hdx : ∀ a s b t, d b t * x a s = x a s * d b t + if a = b ∧ s = t then 1 else 0)
    {k : ℕ} (r g : Fin k → I) (a b : I) :
    Eop x d a b * Pn x d r g = Pn x d (Fin.cons a r) (Fin.cons b g) +
      ∑ j, if r j = b then Pn x d (Function.update r j a) g else 0 := by sorry
