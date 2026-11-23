-- Prove2me | Theorems.Thm_PI_QuotInvW_avgS_ne_zero
-- name    : PI.QuotInvW.avgS_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:39:27.542515+00:00
-- url     : https://prove2.me/theorems/dd91182b-4e44-42f5-a8b9-55e12069d4d9
-- title:
--   Quot Inv W: avg S ne zero
-- statement:
--   The Quot Inv W construction uses the avg S ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientInvariantMeasurability/MeasurableAvgS.lean#L30-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientInvariantMeasurability/MeasurableAvgS.lean#L30-L38

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableMmRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableAvgS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal NNReal
noncomputable section
open PI PI.QuotInvW
variable {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μG μS ν : Measure (MtM m)}

theorem PI.QuotInvW.avgS_ne_zero (h : QuotientSetting G S μG μS ν) {f : MtM m → ℝ≥0∞} (hf : Measurable f)
    (hpos : ∀ x, f x ≠ 0) (x : MtM m) : avgS μS f x ≠ 0 := by sorry
