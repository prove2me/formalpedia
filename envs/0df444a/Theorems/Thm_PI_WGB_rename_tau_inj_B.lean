-- Prove2me | Theorems.Thm_PI_WGB_rename_tau_inj_B
-- name    : PI.WGB.rename_tau_inj_B
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:45:29.061144+00:00
-- url     : https://prove2.me/theorems/b5624a1c-e14d-4b71-ae10-5445e49b3f8b
-- title:
--   WGB: rename tau inj B
-- statement:
--   The WGB construction uses the rename tau inj B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/RenameTauHomogB.lean#L127-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/RenameTauHomogB.lean#L127-L136

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

theorem PI.WGB.rename_tau_inj_B {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j) :
    Function.Injective (rename (R := ℂ) (fun v : Fin N × Fin N => (tauB h σ v.1, v.2))) := by sorry
