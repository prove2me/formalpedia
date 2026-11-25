-- Prove2me | Theorems.Thm_PI_AmpRootCommon_Tri_measurable_extNe
-- name    : PI.AmpRootCommon.Tri.measurable_extNe
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:23:01.889469+00:00
-- url     : https://prove2.me/theorems/64b45930-330c-4e33-8d32-5244dc364b26
-- title:
--   Tri: measurable ext Ne
-- statement:
--   The Tri construction uses the measurable ext Ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/TriShear.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/TriShear.lean#L13-L19

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_TriDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_TriShear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
noncomputable section
open PI PI.AmpRootCommon PI.AmpRootCommon.Tri

theorem PI.AmpRootCommon.Tri.measurable_extNe {ι : Type} [DecidableEq ι] (a : ι) : Measurable (extNe a) := by sorry
