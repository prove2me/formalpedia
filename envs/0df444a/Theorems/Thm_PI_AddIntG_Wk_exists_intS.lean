-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_exists_intS
-- name    : PI.AddIntG.Wk.exists_intS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:57:16.991584+00:00
-- url     : https://prove2.me/theorems/2403976a-0e5c-4912-bec6-1ceb1a4a9a2e
-- title:
--   Wk: exists int S
-- statement:
--   The Wk construction uses the exists int S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/GlueHoldsVar.lean#L223-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/GlueHoldsVar.lean#L223-L249

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GuLine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GlueHoldsVar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.AddIntG PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]

theorem PI.AddIntG.Wk.exists_intS (p : ℕ) [Fact p.Prime] : ∃ S : Subring ℂ_[p], ∀ x, x ∈ S ↔ ‖x‖ ≤ 1 := by sorry
