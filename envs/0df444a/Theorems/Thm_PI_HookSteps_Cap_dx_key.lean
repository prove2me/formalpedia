-- Prove2me | Theorems.Thm_PI_HookSteps_Cap_dx_key
-- name    : PI.HookSteps.Cap.dx_key
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:08:25.090221+00:00
-- url     : https://prove2.me/theorems/e385912b-c9c3-56e3-b36e-c5c4381f1833
-- title:
--   Cap: dx key
-- statement:
--   The Cap construction uses the dx key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/CapelliAbs.lean#L43-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/CapelliAbs.lean#L43-L88

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

theorem PI.HookSteps.Cap.dx_key (x d : I → S → 𝒰) (hxx : ∀ a s b t, x a s * x b t = x b t * x a s)
    (hdx : ∀ a s b t, d b t * x a s = x a s * d b t + if a = b ∧ s = t then 1 else 0) :
    ∀ (k : ℕ) (r : Fin k → I) (s : Fin k → S) (a b : I) (t : S),
      x a t * (d b t * xw x r s) = x a t * xw x r s * d b t +
        ∑ j, if r j = b ∧ s j = t then xw x (Function.update r j a) s else 0 := by sorry
