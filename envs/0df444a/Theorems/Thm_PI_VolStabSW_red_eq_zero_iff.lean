-- Prove2me | Theorems.Thm_PI_VolStabSW_red_eq_zero_iff
-- name    : PI.VolStabSW.red_eq_zero_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:06:46.578132+00:00
-- url     : https://prove2.me/theorems/8fd05284-0e83-4024-b228-df5fd2d3f61c
-- title:
--   Vol Stab SW: red eq zero iff
-- statement:
--   The Vol Stab SW construction uses the red eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensCntRes.lean#L242-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensCntRes.lean#L242-L245

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensCntRes
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
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem PI.VolStabSW.red_eq_zero_iff {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) :
    red v x = 0 ↔ Valued.v x < 1 := by sorry
