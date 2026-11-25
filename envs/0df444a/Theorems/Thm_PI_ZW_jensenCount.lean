-- Prove2me | Theorems.Thm_PI_ZW_jensenCount
-- name    : PI.ZW.jensenCount
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:58:49.924799+00:00
-- url     : https://prove2.me/theorems/6b5a8f37-0fe7-4862-bbf8-e263fd95dec7
-- title:
--   ZW: jensen Count
-- statement:
--   The ZW construction uses the jensen Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/Jensen.lean#L26-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/Jensen.lean#L26-L116

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightHalfWith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_Jensen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric
open PI PI.ZW

theorem PI.ZW.jensenCount : JensenCount := by sorry
