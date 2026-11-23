-- Prove2me | Theorems.Thm_PI_CubicExponentialFactor_Wk_term_int
-- name    : PI.CubicExponentialFactor.Wk.term_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:24.282007+00:00
-- url     : https://prove2.me/theorems/6ef6cf58-e348-4d71-b5dc-b3d1b7fa013b
-- title:
--   Wk: term int
-- statement:
--   The Wk construction uses the term int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubicExponentialFactor/NormAddLeOne.lean#L33-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubicExponentialFactor/NormAddLeOne.lean#L33-L41

import Definitions.Def_Formalism_PeriodIntegrals_CubicExponentialFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubicExponentialFactor_NormAddLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CubicExponentialFactor PI.CubicExponentialFactor.Wk
open PI.CubicExponentialFactor
variable {p : ℕ} [Fact p.Prime]

theorem PI.CubicExponentialFactor.Wk.term_int {a : ℂ_[p]} (ha : ‖a‖ ≤ 1) {m k : ℕ} (hm : 1 ≤ m) {F : PowerSeries ℂ_[p]}
    (hF : ∀ j < k, ‖PowerSeries.coeff j F‖ ≤ 1) :
    ‖PowerSeries.coeff k (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a * PowerSeries.X ^ m * F)‖ ≤ 1 := by sorry
