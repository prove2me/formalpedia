-- Prove2me | Theorems.Thm_PI_WittUnramWork_psi_surjective
-- name    : PI.WittUnramWork.psi_surjective
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:45:15.266428+00:00
-- url     : https://prove2.me/theorems/352f7604-1240-55d4-a288-616078ab7e4c
-- title:
--   Witt Unram Work: psi surjective
-- statement:
--   The Witt Unram Work construction uses the psi surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittUnramified/PsiStep.lean#L46-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittUnramified/PsiStep.lean#L46-L99

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

theorem PI.WittUnramWork.psi_surjective (ψ : W →+* WittVector p k) (res : W →+* k) (hres : Function.Surjective res)
    (h0 : ∀ x, (ψ x).coeff 0 = res x) (hC : IsAdicComplete (Ideal.span {(p : W)}) W) :
    Function.Surjective ψ := by sorry
