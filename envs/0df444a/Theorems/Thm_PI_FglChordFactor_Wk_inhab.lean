-- Prove2me | Theorems.Thm_PI_FglChordFactor_Wk_inhab
-- name    : PI.FglChordFactor.Wk.inhab
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:45:48.199919+00:00
-- url     : https://prove2.me/theorems/ae7ebbda-5b11-5888-b5a1-ba8516120522
-- title:
--   Wk: inhab
-- statement:
--   The Wk construction uses the inhab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupChords/NormDeltaWc.lean#L54-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupChords/NormDeltaWc.lean#L54-L70

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglChordFactor
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_AddIntG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_NormDeltaWc
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
open PI PI.FglChordFactor PI.FglChordFactor.Wk

theorem PI.FglChordFactor.Wk.inhab : ∃ (W : WeierstrassCurve ℂ_[2]) (wq ex : PowerSeries ℂ_[2]),
    IsIntP W.a₁ ∧ IsIntP W.a₂ ∧ IsIntP W.a₃ ∧ IsIntP W.a₄ ∧ IsIntP W.a₆ ∧ ‖W.Δ‖ = 1 ∧
    IsWq W wq ∧ PowerSeries.constantCoeff ex = 0 ∧ PowerSeries.subst ex (flog W wq) = PowerSeries.X ∧
    IntegralMv (add (flog W wq) ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[2]) := by sorry
