-- Prove2me | Theorems.Thm_PI_JetsPhW_Low_coeff_truncatedExp_of_degree_eq_one
-- name    : PI.JetsPhW.Low.coeff_truncatedExp_of_degree_eq_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:09:36.529011+00:00
-- url     : https://prove2.me/theorems/a3149f19-4e71-57d4-a889-d15ac006b955
-- title:
--   Low: coeff truncated Exp of degree eq one
-- statement:
--   The Low construction uses the coeff truncated Exp of degree eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/ExpLow.lean#L13-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/ExpLow.lean#L13-L26

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffSubstOfDegreeEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_ExpLow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.JetsPhW PI.JetsPhW.Low
open PI.JetsPhW
variable {p : ℕ} [Fact p.Prime]

theorem PI.JetsPhW.Low.coeff_truncatedExp_of_degree_eq_one {σ : Type*} (F : MvPowerSeries σ ℂ_[p]) {e : σ →₀ ℕ}
    (hd : Finsupp.degree e = 1) :
    MvPowerSeries.coeff e (expMv F) = MvPowerSeries.coeff e F := by sorry
