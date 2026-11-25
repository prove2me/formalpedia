-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_ZI_cF_bound
-- name    : PI.UnitaryGroupMassFormula.UsCost.ZI.cF_bound
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:41:17.450062+00:00
-- url     : https://prove2.me/theorems/0115ce38-e933-42a6-83cb-470a63bd6b5c
-- title:
--   ZI: c F bound
-- statement:
--   The ZI construction uses the c F bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ZIterB.lean#L115-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ZIterB.lean#L115-L167

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.ZI
variable (s : ℕ)

theorem PI.UnitaryGroupMassFormula.UsCost.ZI.cF_bound (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ Z : Fin s → Fin s → ℂ, (Matrix.of Z).det ≠ 0 → ∀ i, ∀ a ≤ n,
    ‖iteratedFDeriv ℝ a (cF s i) Z‖ ≤ K * (max 1 ‖eA s‖ * max 1 ‖Ring.inverse (eA s Z)‖) ^ (a + 1) := by sorry
