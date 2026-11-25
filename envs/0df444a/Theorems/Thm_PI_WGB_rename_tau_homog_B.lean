-- Prove2me | Theorems.Thm_PI_WGB_rename_tau_homog_B
-- name    : PI.WGB.rename_tau_homog_B
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:48:23.943859+00:00
-- url     : https://prove2.me/theorems/a2f0dafd-36b1-4a58-b4f9-2a28f6f9e849
-- title:
--   WGB: rename tau homog B
-- statement:
--   The WGB construction uses the rename tau homog B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/RenameTauHomogB.lean#L119-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/RenameTauHomogB.lean#L119-L125

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

theorem PI.WGB.rename_tau_homog_B {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j)
    (g : MvPolynomial (Fin N × Fin N) ℂ) (m : Fin n → ℕ) (hg : IsWeightedHomogeneous (wnB n N) g m) :
    IsWeightedHomogeneous (wnB n N) (rename (fun v : Fin N × Fin N => (tauB h σ v.1, v.2)) g)
      (fun j => m (σ j)) := by sorry
