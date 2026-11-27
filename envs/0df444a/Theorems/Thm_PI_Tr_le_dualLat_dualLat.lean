-- Prove2me | Theorems.Thm_PI_Tr_le_dualLat_dualLat
-- name    : PI.Tr.le_dualLat_dualLat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:48:08.484204+00:00
-- url     : https://prove2.me/theorems/16a87577-4f2a-4f0b-9ed7-9e07ba629f6e
-- title:
--   Tr: le dual Lat dual Lat
-- statement:
--   The Tr construction uses the le dual Lat dual Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeTransference/InstIsZLatticeDualLat.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeTransference/InstIsZLatticeDualLat.lean#L29-L35

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_DualTransport
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_InstIsZLatticeDualLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open PI PI.Tr
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem PI.Tr.le_dualLat_dualLat (Λ : Submodule ℤ E) : Λ ≤ dualLat (dualLat Λ) := by sorry
