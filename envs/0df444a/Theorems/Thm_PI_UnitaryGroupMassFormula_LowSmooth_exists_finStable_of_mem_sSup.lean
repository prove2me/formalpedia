-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LowSmooth_exists_finStable_of_mem_sSup
-- name    : PI.UnitaryGroupMassFormula.LowSmooth.exists_finStable_of_mem_sSup
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:05:16.656255+00:00
-- url     : https://prove2.me/theorems/56bc4418-0ac6-599c-96ca-69454cb52d70
-- title:
--   Low Smooth: exists fin Stable of mem s Sup
-- statement:
--   The Low Smooth construction uses the exists fin Stable of mem s Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerSmoothStability/ExistsFinStableOfMemSSup.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerSmoothStability/ExistsFinStableOfMemSSup.lean#L38-L41

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

theorem PI.UnitaryGroupMassFormula.LowSmooth.exists_finStable_of_mem_sSup (G : Set ι) (ρ : ι → H →L[ℂ] H) {F : Set (Submodule ℂ H)}
    (hF : F ⊆ FinStable G ρ) {x : H} (hx : x ∈ sSup F) : ∃ S ∈ FinStable G ρ, x ∈ S := by sorry
