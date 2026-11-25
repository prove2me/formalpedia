-- Prove2me | Theorems.Thm_PI_ZW_sphere_facts
-- name    : PI.ZW.sphere_facts
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:46:48.89901+00:00
-- url     : https://prove2.me/theorems/b837d50d-e2ef-4e35-b6a7-b77c84892e58
-- title:
--   ZW: sphere facts
-- statement:
--   The ZW construction uses the sphere facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/RightChi.lean#L32-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/RightChi.lean#L32-L45

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightHalfWith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightChi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric Complex
open PI PI.ZW

theorem PI.ZW.sphere_facts {z : ℂ} {t : ℝ} (hz : z ∈ sphere (2 + t * I) (19 / 10)) :
    1 / 10 ≤ z.re ∧ ‖z‖ ≤ |t| + 4 := by sorry
