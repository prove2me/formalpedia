-- Prove2me | Theorems.Thm_PI_WGB_wnB_tau
-- name    : PI.WGB.wnB_tau
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:47:30.694797+00:00
-- url     : https://prove2.me/theorems/eb377b30-40c9-4e44-a2a6-1821ea19b748
-- title:
--   WGB: wn B tau
-- statement:
--   The WGB construction uses the wn B tau property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/RenameTauHomogB.lean#L91-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/RenameTauHomogB.lean#L91-L106

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

theorem PI.WGB.wnB_tau {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j)
    (v : Fin N × Fin N) : wnB n N (tauB h σ v.1, v.2) = fun j => wnB n N v (σ j) := by sorry
