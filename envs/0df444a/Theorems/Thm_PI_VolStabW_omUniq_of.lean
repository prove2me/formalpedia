-- Prove2me | Theorems.Thm_PI_VolStabW_omUniq_of
-- name    : PI.VolStabW.omUniq_of
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:47:06.591128+00:00
-- url     : https://prove2.me/theorems/6596ccc0-d579-4240-8d0f-34900ce4eee6
-- title:
--   Vol Stab W: om Uniq of
-- statement:
--   The Vol Stab W construction uses the om Uniq of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/NuInvSt.lean#L42-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/NuInvSt.lean#L42-L57

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoNuFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_NuInvSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal

theorem PI.VolStabW.omUniq_of (hD : DetAdm) : OmUniq := by sorry
