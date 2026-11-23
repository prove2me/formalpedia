-- Prove2me | Theorems.Thm_PI_AmpRootCommon_tau_cs
-- name    : PI.AmpRootCommon.tau_cs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:22.624047+00:00
-- url     : https://prove2.me/theorems/bff1b294-26b0-4e73-bf9d-b89b9f52186c
-- title:
--   Amp Root Common: tau cs
-- statement:
--   The Amp Root Common construction uses the tau cs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/SuperdiagPairingAdjacent.lean#L151-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/SuperdiagPairingAdjacent.lean#L151-L153

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_SuperdiagPairingAdjacent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.AmpRootCommon
variable {n : ℕ}
variable {m : ℕ}

theorem PI.AmpRootCommon.tau_cs {σ : Fin (m + 1) → Fin (m + 1)} {i : Fin m} (h : (σ i.succ).val + 1 = (σ i.castSucc).val) :
    (tau σ i).castSucc = σ i.succ := by sorry
