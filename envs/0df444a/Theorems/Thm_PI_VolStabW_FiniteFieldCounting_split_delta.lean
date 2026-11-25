-- Prove2me | Theorems.Thm_PI_VolStabW_FiniteFieldCounting_split_delta
-- name    : PI.VolStabW.FiniteFieldCounting.split_delta
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:37:43.367432+00:00
-- url     : https://prove2.me/theorems/825d010e-0176-4410-97ab-a35933448a67
-- title:
--   Finite Field Counting: split delta
-- statement:
--   The Finite Field Counting construction uses the split delta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensFFT.lean#L95-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensFFT.lean#L95-L107

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

theorem PI.VolStabW.FiniteFieldCounting.split_delta (M a : ℕ) (ha : a + 2 ≤ M) (q : ℝ) (hq : 1 ≤ q) (i : Fin a) :
    |-(q ^ (i : ℕ) / q ^ M)| ≤ (q⁻¹) ^ 2 := by sorry
