-- Prove2me | Theorems.Thm_PI_AmpRootCommon_superdiagPairing_adjacent
-- name    : PI.AmpRootCommon.superdiagPairing_adjacent
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:23:14.823445+00:00
-- url     : https://prove2.me/theorems/09efc0fe-bb3f-4487-81be-b47691301959
-- title:
--   Amp Root Common: superdiag Pairing adjacent
-- statement:
--   The Amp Root Common construction uses the superdiag Pairing adjacent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/SuperdiagPairingAdjacent.lean#L159-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/SuperdiagPairingAdjacent.lean#L159-L162

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

theorem PI.AmpRootCommon.superdiagPairing_adjacent {σ : Fin (m + 1) → Fin (m + 1)} (hσ : ∀ i, σ (σ i) = i) {i : Fin m}
    (h : (σ i.succ).val + 1 = (σ i.castSucc).val) :
    (σ (tau σ i).succ).val + 1 = (σ (tau σ i).castSucc).val := by sorry
