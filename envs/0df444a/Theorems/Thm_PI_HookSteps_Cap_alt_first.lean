-- Prove2me | Theorems.Thm_PI_HookSteps_Cap_alt_first
-- name    : PI.HookSteps.Cap.alt_first
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:08:02.926634+00:00
-- url     : https://prove2.me/theorems/be2bf44a-b768-4972-98c7-eb83a67abcca
-- title:
--   Cap: alt first
-- statement:
--   The Cap construction uses the alt first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/CapelliMain.lean#L56-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/CapelliMain.lean#L56-L72

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

theorem PI.HookSteps.Cap.alt_first {k : ℕ} (F : I → 𝒰) (Δ : (Fin k → I) → 𝒰) (r : Fin (k + 1) → I)
    (hIH : ∀ r' : Fin k → I,
      ∑ τ : Equiv.Perm (Fin k), ((Equiv.Perm.sign τ : ℤˣ) : ℤ) • Δ (fun j => r' (τ j)) = 0) :
    ∑ σ : Equiv.Perm (Fin (k + 1)), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
      (F (r (σ 0)) * Δ (fun i => r (σ i.succ))) = 0 := by sorry
