-- Prove2me | Theorems.Thm_PI_ZW_analyticAt_riemannZeta_of_ne
-- name    : PI.ZW.analyticAt_riemannZeta_of_ne
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:46:44.463563+00:00
-- url     : https://prove2.me/theorems/ba7e2fed-a02d-4936-a967-89a87f840731
-- title:
--   ZW: analytic At riemann Zeta of ne
-- statement:
--   The ZW construction uses the analytic At riemann Zeta of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/RightOne.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/RightOne.lean#L22-L24

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightChi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric Complex Filter Topology
open PI PI.ZW

theorem PI.ZW.analyticAt_riemannZeta_of_ne {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by sorry
