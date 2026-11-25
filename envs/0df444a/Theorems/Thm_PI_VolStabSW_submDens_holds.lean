-- Prove2me | Theorems.Thm_PI_VolStabSW_submDens_holds
-- name    : PI.VolStabSW.submDens_holds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:55.902249+00:00
-- url     : https://prove2.me/theorems/57da33fb-1e07-4306-a14e-70b4a49a9577
-- title:
--   Vol Stab SW: subm Dens holds
-- statement:
--   The Vol Stab SW construction uses the subm Dens holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/DensInfTop.lean#L10-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/DensInfTop.lean#L10-L10

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfCV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW

theorem PI.VolStabSW.submDens_holds : SubmDens := by sorry
