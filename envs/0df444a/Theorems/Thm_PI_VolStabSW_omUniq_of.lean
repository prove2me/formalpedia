-- Prove2me | Theorems.Thm_PI_VolStabSW_omUniq_of
-- name    : PI.VolStabSW.omUniq_of
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:45:06.994799+00:00
-- url     : https://prove2.me/theorems/eff82c15-34c7-4fd5-8db5-e843ed300c5a
-- title:
--   Vol Stab SW: om Uniq of
-- statement:
--   The Vol Stab SW construction uses the om Uniq of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/NuInvSt.lean#L42-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/NuInvSt.lean#L42-L57

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoNuFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_NuInvSt
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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal

theorem PI.VolStabSW.omUniq_of (hD : DetAdm) : OmUniq := by sorry
