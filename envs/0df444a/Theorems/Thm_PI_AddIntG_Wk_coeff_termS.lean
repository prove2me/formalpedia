-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_coeff_termS
-- name    : PI.AddIntG.Wk.coeff_termS
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:22:13.783818+00:00
-- url     : https://prove2.me/theorems/4ab0cc65-31ab-5d0e-8696-8855af93ae7a
-- title:
--   Wk: coeff term S
-- statement:
--   The Wk construction uses the coeff term S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/CoeffPowMemS.lean#L41-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/CoeffPowMemS.lean#L41-L45

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GuLine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffPowMemS
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

theorem PI.AddIntG.Wk.coeff_termS (a : ℂ_[p]) (k n : ℕ) (f : PowerSeries ℂ_[p]) :
    PowerSeries.coeff n (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a * PowerSeries.X ^ k * f) =
      if k ≤ n then a * PowerSeries.coeff (n - k) f else 0 := by sorry
