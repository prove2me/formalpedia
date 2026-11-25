-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_lamA_single0
-- name    : PI.AddIntG.Wk.lamA_single0
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:22:08.767361+00:00
-- url     : https://prove2.me/theorems/5c64fb45-14bd-4e3c-8ed0-f6b34a5ff1dd
-- title:
--   Wk: lam A single0
-- statement:
--   The Wk construction uses the lam A single0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/CoeffWSeriesVarZero.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/CoeffWSeriesVarZero.lean#L18-L21

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

theorem PI.AddIntG.Wk.lamA_single0 (e : Fin 2 →₀ ℕ) : e = Finsupp.single 0 (e 0) ↔ e 1 = 0 := by sorry
