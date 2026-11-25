-- Prove2me | Theorems.Thm_PI_JetsPhW_W_Dv_sub
-- name    : PI.JetsPhW.W.Dv_sub
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:33:58.757933+00:00
-- url     : https://prove2.me/theorems/bb19615d-14e7-429d-8ae9-d32b8fdd836b
-- title:
--   W: Dv sub
-- statement:
--   The W construction uses the Dv sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/HighGOf.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/HighGOf.lean#L16-L18

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_PolarizationDifferenceFormulaHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_HighGOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.JetsPhW PI.JetsPhW.W
open PI.JetsPhW
variable {p : ℕ} [Fact p.Prime] {σ : Type*}

theorem PI.JetsPhW.W.Dv_sub (v : PowerSeries ℂ_[p]) (i : σ) (f g : MvPowerSeries σ ℂ_[p]) :
    Dv v i (f - g) = Dv v i f - Dv v i g := by sorry
