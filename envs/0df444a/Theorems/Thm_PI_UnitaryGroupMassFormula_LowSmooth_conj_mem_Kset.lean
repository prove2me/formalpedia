-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LowSmooth_conj_mem_Kset
-- name    : PI.UnitaryGroupMassFormula.LowSmooth.conj_mem_Kset
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:29:31.008501+00:00
-- url     : https://prove2.me/theorems/f58e08c6-24b9-40f6-a9e4-9a953e58626a
-- title:
--   Low Smooth: conj mem Kset
-- statement:
--   The Low Smooth construction uses the conj mem Kset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerSmoothStability/ExistsFinStableOfMemSSup.lean#L49-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerSmoothStability/ExistsFinStableOfMemSSup.lean#L49-L93

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
variable {k r : ℕ}

theorem PI.UnitaryGroupMassFormula.LowSmooth.conj_mem_Kset {ε : Fin (2 * r + k + 1) → Bool} {P g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : IsCayleyU k r ε P)
    (hg : g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _)) :
    P * g * P⁻¹ ∈ Kset ε ∧ P⁻¹ * (P * g * P⁻¹) * P = g := by sorry
