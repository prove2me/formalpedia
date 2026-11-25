-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LowSmooth_isKFinHpk_of_lowUnit
-- name    : PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:44:36.725908+00:00
-- url     : https://prove2.me/theorems/bf977624-8737-4542-967a-e86966b2c68c
-- title:
--   Low Smooth: is KFin Hpk of low Unit
-- statement:
--   The Low Smooth construction uses the is KFin Hpk of low Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerSmoothStability/ExistsFinStableOfMemSSup.lean#L97-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerSmoothStability/ExistsFinStableOfMemSSup.lean#L97-L109

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

theorem PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} {w : H}
    (hlow : IsLowUnitH k r ε lam σ w) : IsKFinHpk (k := k) (r := r) σ w := by sorry
