-- Prove2me | Theorems.Thm_PI_OkpW_ultra_limit
-- name    : PI.OkpW.ultra_limit
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:35:59.133664+00:00
-- url     : https://prove2.me/theorems/33dd6114-7781-5a3a-9d22-9959dc4422e3
-- title:
--   Okp W: ultra limit
-- statement:
--   The Okp W construction uses the ultra limit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/DvdPowQSub.lean#L26-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/DvdPowQSub.lean#L26-L35

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

theorem PI.OkpW.ultra_limit {E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E] [CompleteSpace E]
    (x : ℕ → E) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (h : ∀ k, ‖x (k + 1) - x k‖ ≤ r ^ (k + 1)) :
    Tendsto x atTop (𝓝 (limUnder atTop x)) ∧ ∀ k, ‖limUnder atTop x - x k‖ ≤ r ^ (k + 1) := by sorry
