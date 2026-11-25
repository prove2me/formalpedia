-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_lamA_single1
-- name    : PI.AddIntG.Wk.lamA_single1
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:23:00.682435+00:00
-- url     : https://prove2.me/theorems/ef2bce93-5ede-4db9-9f8d-8984640fedf4
-- title:
--   Wk: lam A single1
-- statement:
--   The Wk construction uses the lam A single1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/CoeffWSeriesVarZero.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/CoeffWSeriesVarZero.lean#L23-L26

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffPowMemS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
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

theorem PI.AddIntG.Wk.lamA_single1 (e : Fin 2 →₀ ℕ) : e = Finsupp.single 1 (e 1) ↔ e 0 = 0 := by sorry
