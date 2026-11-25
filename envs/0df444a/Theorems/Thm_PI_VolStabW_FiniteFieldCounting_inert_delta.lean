-- Prove2me | Theorems.Thm_PI_VolStabW_FiniteFieldCounting_inert_delta
-- name    : PI.VolStabW.FiniteFieldCounting.inert_delta
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:37:39.970805+00:00
-- url     : https://prove2.me/theorems/b1476a8b-9a23-4a8a-ab7b-a3476bfcd163
-- title:
--   Finite Field Counting: inert delta
-- statement:
--   The Finite Field Counting construction uses the inert delta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensFFT.lean#L109-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensFFT.lean#L109-L122

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

theorem PI.VolStabW.FiniteFieldCounting.inert_delta (M a : ℕ) (ha : a + 2 ≤ M) (q : ℝ) (hq : 1 ≤ q) (j : Fin a) :
    |-((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))| ≤ (q⁻¹) ^ 2 := by sorry
