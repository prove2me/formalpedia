-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_SR_sr1_prod
-- name    : PI.VolSemiDirect.W.SR.sr1_prod
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:37:01.825097+00:00
-- url     : https://prove2.me/theorems/9aeff18b-600b-4f0f-a0f6-c9fbdeaa1efa
-- title:
--   SR: sr1 prod
-- statement:
--   The SR construction uses the sr1 prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/HasStableRangeOne.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/HasStableRangeOne.lean#L11-L16

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HasStableRangeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.SR
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped RestrictedProduct

theorem PI.VolSemiDirect.W.SR.sr1_prod {A B : Type} [CommRing A] [CommRing B] (hA : Cj.HasStableRangeOne A) (hB : Cj.HasStableRangeOne B) :
    Cj.HasStableRangeOne (A × B) := by sorry
