-- Prove2me | Theorems.Thm_PI_WGB_rowAct_swap_B
-- name    : PI.WGB.rowAct_swap_B
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:45:38.213897+00:00
-- url     : https://prove2.me/theorems/4c14cf46-c27e-471f-9182-f3aa66e63046
-- title:
--   WGB: row Act swap B
-- statement:
--   The WGB construction uses the row Act swap B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/RenameTauHomogB.lean#L78-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/RenameTauHomogB.lean#L78-L89

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

theorem PI.WGB.rowAct_swap_B {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := N)
              (((embGL ℂ n N h (swapGL σ hσ) : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).transpose) =
      rename (fun v : Fin N × Fin N => (tauB h σ v.1, v.2)) := by sorry
