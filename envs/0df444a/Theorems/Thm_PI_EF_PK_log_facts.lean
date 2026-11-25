-- Prove2me | Theorems.Thm_PI_EF_PK_log_facts
-- name    : PI.EF.PK.log_facts
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:27:47.537028+00:00
-- url     : https://prove2.me/theorems/21c10c2e-827d-5ce6-beec-64020f6c57b7
-- title:
--   PK: log facts
-- statement:
--   The PK construction uses the log facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/ContinuousInvSqrt.lean#L95-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/ContinuousInvSqrt.lean#L95-L127

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronTruncOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ContinuousInvSqrt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.PK
open Complex MeasureTheory intervalIntegral Real

theorem PI.EF.PK.log_facts {N : ℕ} {u T T' : ℝ} (hN : (1 : ℝ) ≤ N) (hT : 2 ≤ T) (hTu : T ≤ u) (hTT' : T ≤ T')
    (hT'1 : T' ≤ T + 1) :
    0 ≤ Real.log (N * u * T) ∧ Real.log (N * T') ≤ Real.log (N * u * T) ∧
      0 ≤ Real.log (N * T') ∧ Real.log (N * (T' + 2)) ≤ 2 * Real.log (N * u * T) ∧
      Real.log (1 + 2 * (2 * T')) ≤ 2 * Real.log (N * u * T) ∧ 0 ≤ Real.log (N * (T' + 2)) ∧
      0 ≤ Real.log (N * u) := by sorry
