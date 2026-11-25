-- Prove2me | Theorems.Thm_PI_SSE_sigmaStarEx_of_parts
-- name    : PI.SSE.sigmaStarEx_of_parts
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:20:12.295803+00:00
-- url     : https://prove2.me/theorems/c4425ddf-004d-56df-a6af-4d3691fd4e09
-- title:
--   SSE: sigma Star Ex of parts
-- statement:
--   The SSE construction uses the sigma Star Ex of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesExistence/Development.lean#L65-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesExistence/Development.lean#L65-L67

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatDefs
import Definitions.Def_Formalism_PeriodIntegrals_SigmaStarEx
import Definitions.Def_Formalism_PeriodIntegrals_AreaLat
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_AreaLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Classical
open PI PI.SSE

theorem PI.SSE.sigmaStarEx_of_parts (ha : ThetaA) (hb : ThetaDerivNe) (hr : ReduceBasis)
    (hn : GenEqOf) (hl : LatExt) : PI.SigmaStarEx := by sorry
