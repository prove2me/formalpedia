-- Prove2me | Theorems.Thm_PI_AmpRootCommon_tau_neg
-- name    : PI.AmpRootCommon.tau_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:17.078421+00:00
-- url     : https://prove2.me/theorems/baa585f7-fdb3-4a55-9687-3fe3a5948791
-- title:
--   Amp Root Common: tau neg
-- statement:
--   The Amp Root Common construction uses the tau neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/SuperdiagPairingAdjacent.lean#L147-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/SuperdiagPairingAdjacent.lean#L147-L149

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

theorem PI.AmpRootCommon.tau_neg {σ : Fin (m + 1) → Fin (m + 1)} {i : Fin m} (h : ¬ (σ i.succ).val + 1 = (σ i.castSucc).val) :
    tau σ i = i := by sorry
