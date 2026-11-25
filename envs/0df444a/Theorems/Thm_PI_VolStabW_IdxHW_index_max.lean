-- Prove2me | Theorems.Thm_PI_VolStabW_IdxHW_index_max
-- name    : PI.VolStabW.IdxHW.index_max
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:42:06.033958+00:00
-- url     : https://prove2.me/theorems/31967e3e-894d-47d1-929a-fa708b5e189a
-- title:
--   Idx HW: index max
-- statement:
--   The Idx HW construction uses the index max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensIdxE.lean#L111-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensIdxE.lean#L111-L114

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxE
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
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  IsLocalRing
open PI.VolStabW.IdxHW

theorem PI.VolStabW.IdxHW.index_max {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (maximalIdeal (v.adicCompletionIntegers F)).toAddSubgroup.index = Nat.card (𝓞 F ⧸ v.asIdeal) := by sorry
