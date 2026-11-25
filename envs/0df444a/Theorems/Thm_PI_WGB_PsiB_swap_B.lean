-- Prove2me | Theorems.Thm_PI_WGB_PsiB_swap_B
-- name    : PI.WGB.PsiB_swap_B
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:48:57.327476+00:00
-- url     : https://prove2.me/theorems/a280e948-cb26-4858-b1df-3af46801d539
-- title:
--   WGB: Psi B swap B
-- statement:
--   The WGB construction uses the Psi B swap B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/RenameTauHomogB.lean#L148-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/RenameTauHomogB.lean#L148-L172

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_DetPowUnitriB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RenameTauHomogB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions MvPolynomial

theorem PI.WGB.PsiB_swap_B {n : ℕ} (m : Fin n → ℕ) (i : ℕ) (hi : i + 1 < n)
    (hlt : m ⟨i, by omega⟩ < m ⟨i + 1, hi⟩) :
    PsiB n m < PsiB n (fun j => m (Equiv.swap (⟨i, by omega⟩ : Fin n) ⟨i + 1, hi⟩ j)) := by sorry
