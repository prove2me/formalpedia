-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_lamA_coeff_mul_X
-- name    : PI.AddIntG.Wk.lamA_coeff_mul_X
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:22:08.443077+00:00
-- url     : https://prove2.me/theorems/ae4b99ed-ea36-4084-a0cd-297053b1ccf3
-- title:
--   Wk: lam A coeff mul X
-- statement:
--   The Wk construction uses the lam A coeff mul X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/CoeffWSeriesVarZero.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/CoeffWSeriesVarZero.lean#L38-L43

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

theorem PI.AddIntG.Wk.lamA_coeff_mul_X (f : MvPowerSeries (Fin 2) ℂ_[p]) (i : Fin 2) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (f * Xv i) =
      if 1 ≤ e i then MvPowerSeries.coeff (e - Finsupp.single i 1) f else 0 := by sorry
