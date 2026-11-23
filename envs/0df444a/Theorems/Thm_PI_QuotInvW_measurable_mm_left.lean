-- Prove2me | Theorems.Thm_PI_QuotInvW_measurable_mm_left
-- name    : PI.QuotInvW.measurable_mm_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:29:27.338263+00:00
-- url     : https://prove2.me/theorems/c062cb1a-6a7d-4b8a-9877-a86b29efa54e
-- title:
--   Quot Inv W: measurable mm left
-- statement:
--   The Quot Inv W construction uses the measurable mm left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientInvariantMeasurability/MeasurableMmRight.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientInvariantMeasurability/MeasurableMmRight.lean#L23-L24

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

theorem PI.QuotInvW.measurable_mm_left (b : MtM m) : Measurable (fun a : MtM m => mm a b) := by sorry
