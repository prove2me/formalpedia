-- Prove2me | Theorems.Thm_PI_AmpRootCommon_det_unitri
-- name    : PI.AmpRootCommon.det_unitri
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:23:02.890552+00:00
-- url     : https://prove2.me/theorems/3125d1f1-1563-4f33-8cf4-1373f6568e51
-- title:
--   Amp Root Common: det unitri
-- statement:
--   The Amp Root Common construction uses the det unitri property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/SuperdiagPairingAdjacent.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/SuperdiagPairingAdjacent.lean#L11-L13

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

theorem PI.AmpRootCommon.det_unitri {u : Matrix (Fin n) (Fin n) ℂ} (hu : u.BlockTriangular id) (hud : ∀ i, u i i = 1) :
    u.det = 1 := by sorry
