-- Prove2me | Theorems.Thm_PI_WittUnramWork_psi_injective
-- name    : PI.WittUnramWork.psi_injective
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:45:53.027591+00:00
-- url     : https://prove2.me/theorems/7004cdfc-7174-4d5c-9e75-d6a5b4d72c96
-- title:
--   Witt Unram Work: psi injective
-- statement:
--   The Witt Unram Work construction uses the psi injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittUnramified/PsiStep.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittUnramified/PsiStep.lean#L13-L22

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WittUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittUnramified_PsiStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WittUnramWork
open WittVector Finset
variable {p : ℕ} [hp : Fact p.Prime] {W k : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
  [Field k] [CharP k p] [PerfectRing k p]

theorem PI.WittUnramWork.psi_injective (ψ : W →+* WittVector p k) (hirr : Irreducible (p : W)) :
    Function.Injective ψ := by sorry
