-- Prove2me | Theorems.Thm_PI_VolStabS_FiniteFieldCounting_sum_exp
-- name    : PI.VolStabS.FiniteFieldCounting.sum_exp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:36:37.513599+00:00
-- url     : https://prove2.me/theorems/4b729966-97d7-42dc-9d92-3f436a9dfef0
-- title:
--   Finite Field Counting: sum exp
-- statement:
--   The Finite Field Counting construction uses the sum exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensFFT.lean#L59-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensFFT.lean#L59-L79

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

theorem PI.VolStabS.FiniteFieldCounting.sum_exp (M : ℕ) : ∀ a, a ≤ M →
    ∑ j ∈ Finset.range a, (2 * (M - j) - 1) = 2 * M * a - a ^ 2 := by sorry
