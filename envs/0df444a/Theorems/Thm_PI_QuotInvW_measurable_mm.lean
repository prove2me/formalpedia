-- Prove2me | Theorems.Thm_PI_QuotInvW_measurable_mm
-- name    : PI.QuotInvW.measurable_mm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:29:34.880146+00:00
-- url     : https://prove2.me/theorems/9dad08e4-91be-4d0b-b1f9-eccf4a656a51
-- title:
--   Quot Inv W: measurable mm
-- statement:
--   The Quot Inv W construction uses the measurable mm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientInvariantMeasurability/MeasurableMmRight.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientInvariantMeasurability/MeasurableMmRight.lean#L20-L21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableMmRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal
noncomputable section
open PI PI.QuotInvW
variable {m : ℕ}

theorem PI.QuotInvW.measurable_mm : Measurable (fun p : MtM m × MtM m => mm p.1 p.2) := by sorry
