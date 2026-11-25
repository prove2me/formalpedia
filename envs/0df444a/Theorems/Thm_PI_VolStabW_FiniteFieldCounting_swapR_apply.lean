-- Prove2me | Theorems.Thm_PI_VolStabW_FiniteFieldCounting_swapR_apply
-- name    : PI.VolStabW.FiniteFieldCounting.swapR_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:37:38.54446+00:00
-- url     : https://prove2.me/theorems/a3ce2337-ca10-47c1-a86f-36070f06049b
-- title:
--   Finite Field Counting: swap R apply
-- statement:
--   The Finite Field Counting construction uses the swap R apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensFFT.lean#L124-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensFFT.lean#L124-L124

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFT
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
open PI.VolStabW.FiniteFieldCounting

theorem PI.VolStabW.FiniteFieldCounting.swapR_apply (k : Type) [Field k] (y : k × k) : FiniteFieldSplitting.swapR k y = y.swap := by sorry
