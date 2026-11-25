-- Prove2me | Theorems.Thm_PI_OmVe_ffH_sum_right
-- name    : PI.OmVe.ffH_sum_right
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:00:45.530797+00:00
-- url     : https://prove2.me/theorems/100858bb-915a-4e07-a3a1-f4e9f8c0bd26
-- title:
--   Om Ve: ff H sum right
-- statement:
--   The Om Ve construction uses the ff H sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/SingleMulVec.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/SingleMulVec.lean#L32-L37

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_SingleMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmVe
open PI.VolStabSW Matrix
variable {K : Type} [CommRing K] (σ : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)

theorem PI.OmVe.ffH_sum_right {ι : Type} (s : Finset ι) (c : ι → K) (x : Fin M → K) (y : ι → Fin M → K) :
    ffH σ J x (∑ l ∈ s, c l • y l) = ∑ l ∈ s, c l * ffH σ J x (y l) := by sorry
