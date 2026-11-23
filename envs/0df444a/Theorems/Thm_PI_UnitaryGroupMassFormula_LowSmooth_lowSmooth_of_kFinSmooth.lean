-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LowSmooth_lowSmooth_of_kFinSmooth
-- name    : PI.UnitaryGroupMassFormula.LowSmooth.lowSmooth_of_kFinSmooth
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:46:31.950356+00:00
-- url     : https://prove2.me/theorems/d7a1830b-ad58-43e5-a682-e52ca9e284d3
-- title:
--   Low Smooth: low Smooth of k Fin Smooth
-- statement:
--   The Low Smooth construction uses the low Smooth of k Fin Smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerSmoothStability/ExistsFinStableOfMemSSup.lean#L111-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerSmoothStability/ExistsFinStableOfMemSSup.lean#L111-L113

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

theorem PI.UnitaryGroupMassFormula.LowSmooth.lowSmooth_of_kFinSmooth (hK : PI.KFinSmooth) : PI.LowSmooth := by sorry
