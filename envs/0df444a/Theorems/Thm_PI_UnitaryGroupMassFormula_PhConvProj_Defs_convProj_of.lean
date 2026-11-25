-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhConvProj_Defs_convProj_of
-- name    : PI.UnitaryGroupMassFormula.PhConvProj.Defs.convProj_of
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:32:43.380793+00:00
-- url     : https://prove2.me/theorems/c6e29d36-1b3b-4c0f-a02f-01a5a6b1d0be
-- title:
--   Defs: conv Proj of
-- statement:
--   The Defs construction uses the conv Proj of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConvolutionProjection/ConvProjOf.lean#L27-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConvolutionProjection/ConvProjOf.lean#L27-L36

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhConvProj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConvolutionProjection_ConvProjOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhConvProj PI.UnitaryGroupMassFormula.PhConvProj.Defs
open PI.PhConvProj

theorem PI.UnitaryGroupMassFormula.PhConvProj.Defs.convProj_of (h1 : SelfAdjStep) (h2 : SandStep) : ConvProj := by sorry
