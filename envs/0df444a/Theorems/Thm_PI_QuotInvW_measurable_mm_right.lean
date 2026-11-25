-- Prove2me | Theorems.Thm_PI_QuotInvW_measurable_mm_right
-- name    : PI.QuotInvW.measurable_mm_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:39:22.48433+00:00
-- url     : https://prove2.me/theorems/5441b86a-329a-430c-aa15-cda8d7e0fab4
-- title:
--   Quot Inv W: measurable mm right
-- statement:
--   The Quot Inv W construction uses the measurable mm right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientInvariantMeasurability/MeasurableMmRight.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientInvariantMeasurability/MeasurableMmRight.lean#L26-L27

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

theorem PI.QuotInvW.measurable_mm_right (a : MtM m) : Measurable (fun b : MtM m => mm a b) := by sorry
