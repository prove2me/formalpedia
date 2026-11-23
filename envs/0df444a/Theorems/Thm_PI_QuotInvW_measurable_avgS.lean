-- Prove2me | Theorems.Thm_PI_QuotInvW_measurable_avgS
-- name    : PI.QuotInvW.measurable_avgS
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:44:53.875008+00:00
-- url     : https://prove2.me/theorems/f39951a7-7457-4c9d-962a-3ef11c5b647f
-- title:
--   Quot Inv W: measurable avg S
-- statement:
--   The Quot Inv W construction uses the measurable avg S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientInvariantMeasurability/MeasurableAvgS.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientInvariantMeasurability/MeasurableAvgS.lean#L14-L16

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

theorem PI.QuotInvW.measurable_avgS [SFinite μS] {f : MtM m → ℝ≥0∞} (hf : Measurable f) :
    Measurable (avgS μS f) := by sorry
