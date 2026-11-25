-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LowSmooth_finStable_directed
-- name    : PI.UnitaryGroupMassFormula.LowSmooth.finStable_directed
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:32:00.664898+00:00
-- url     : https://prove2.me/theorems/d8836b9d-0ab6-58ce-ae71-bcb8aad6b244
-- title:
--   Low Smooth: fin Stable directed
-- statement:
--   The Low Smooth construction uses the fin Stable directed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerSmoothStability/ExistsFinStableOfMemSSup.lean#L26-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerSmoothStability/ExistsFinStableOfMemSSup.lean#L26-L36

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_LowCyc
import Definitions.Def_Formalism_PeriodIntegrals_KFinSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LowSmooth
open PI.UpqRep
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ι : Type*}

theorem PI.UnitaryGroupMassFormula.LowSmooth.finStable_directed (G : Set ι) (ρ : ι → H →L[ℂ] H) :
    DirectedOn (· ≤ ·) (FinStable G ρ) := by sorry
