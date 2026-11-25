-- Prove2me | Theorems.Thm_PI_VolStabS_FiniteFieldCounting_split_ratio
-- name    : PI.VolStabS.FiniteFieldCounting.split_ratio
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:36:23.883369+00:00
-- url     : https://prove2.me/theorems/ac29a657-473d-4e60-8a0f-b932f60d5435
-- title:
--   Finite Field Counting: split ratio
-- statement:
--   The Finite Field Counting construction uses the split ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensFFT.lean#L81-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensFFT.lean#L81-L94

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open PI.VolStabS.FiniteFieldCounting

theorem PI.VolStabS.FiniteFieldCounting.split_ratio (M a : ℕ) (ha : a ≤ M) (q : ℝ) (hq : q ≠ 0) :
    (∏ i : Fin a, (q ^ M - q ^ (i : ℕ))) * q ^ (a * (M - a)) / q ^ (2 * M * a - a ^ 2) =
      ∏ i : Fin a, (1 + -(q ^ (i : ℕ) / q ^ M)) := by sorry
