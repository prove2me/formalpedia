-- Prove2me | Theorems.Thm_PI_OkpW_ultra_tail
-- name    : PI.OkpW.ultra_tail
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:36:05.583821+00:00
-- url     : https://prove2.me/theorems/fac2d34f-3560-5665-aa03-07ed40d3205a
-- title:
--   Okp W: ultra tail
-- statement:
--   The Okp W construction uses the ultra tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/DvdPowQSub.lean#L10-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/DvdPowQSub.lean#L10-L24

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_CFrob
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_DvdPowQSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
noncomputable section
open PI PI.OkpW

theorem PI.OkpW.ultra_tail {E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E] (x : ℕ → E) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (h : ∀ k, ‖x (k + 1) - x k‖ ≤ r ^ (k + 1)) (k j : ℕ) :
    ‖x (j + k) - x k‖ ≤ r ^ (k + 1) := by sorry
