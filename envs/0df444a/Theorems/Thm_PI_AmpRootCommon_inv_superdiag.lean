-- Prove2me | Theorems.Thm_PI_AmpRootCommon_inv_superdiag
-- name    : PI.AmpRootCommon.inv_superdiag
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:23:03.92419+00:00
-- url     : https://prove2.me/theorems/0462b8f4-fcb7-491f-af85-1481719765c9
-- title:
--   Amp Root Common: inv superdiag
-- statement:
--   The Amp Root Common construction uses the inv superdiag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/SuperdiagPairingAdjacent.lean#L24-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/SuperdiagPairingAdjacent.lean#L24-L56

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

theorem PI.AmpRootCommon.inv_superdiag {u : Matrix (Fin n) (Fin n) ℂ} (hu : u.BlockTriangular id) (hud : ∀ i, u i i = 1)
    (m1 m : Fin n) (hm : m1.val + 1 = m.val) : u⁻¹ m1 m = - u m1 m := by sorry
