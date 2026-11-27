-- Prove2me | Theorems.Thm_PI_Tr_dualZ_eq_dualLat
-- name    : PI.Tr.dualZ_eq_dualLat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:48:44.090799+00:00
-- url     : https://prove2.me/theorems/61c51c36-beec-4aab-9e38-a15d9d117535
-- title:
--   Tr: dual Z eq dual Lat
-- statement:
--   The Tr construction uses the dual Z eq dual Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeTransference/InstIsZLatticeDualLat.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeTransference/InstIsZLatticeDualLat.lean#L23-L27

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

theorem PI.Tr.dualZ_eq_dualLat {N : ℕ} (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))) :
    PI.dualZ M = dualLat M := by sorry
