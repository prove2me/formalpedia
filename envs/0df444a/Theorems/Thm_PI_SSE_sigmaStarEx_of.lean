-- Prove2me | Theorems.Thm_PI_SSE_sigmaStarEx_of
-- name    : PI.SSE.sigmaStarEx_of
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:20:07.912442+00:00
-- url     : https://prove2.me/theorems/fea69237-e496-4158-af61-84e559d3858e
-- title:
--   SSE: sigma Star Ex of
-- statement:
--   The SSE construction uses the sigma Star Ex of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesExistence/Development.lean#L42-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesExistence/Development.lean#L42-L63

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

theorem PI.SSE.sigmaStarEx_of (hR : ReduceBasis) (hG : GenEq) (hL : LatExt) (hA : PI.AreaLat) :
    PI.SigmaStarEx := by sorry
