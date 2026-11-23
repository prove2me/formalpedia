-- Prove2me | Theorems.Thm_PI_AmpRootCommon_isUnit_unitri
-- name    : PI.AmpRootCommon.isUnit_unitri
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:54:45.581409+00:00
-- url     : https://prove2.me/theorems/2366a8d6-be3b-421e-906c-988b626df6c4
-- title:
--   Amp Root Common: is Unit unitri
-- statement:
--   The Amp Root Common construction uses the is Unit unitri property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/SuperdiagPairingAdjacent.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/SuperdiagPairingAdjacent.lean#L15-L17

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

theorem PI.AmpRootCommon.isUnit_unitri {u : Matrix (Fin n) (Fin n) ℂ} (hu : u.BlockTriangular id) (hud : ∀ i, u i i = 1) :
    IsUnit u.det := by sorry
