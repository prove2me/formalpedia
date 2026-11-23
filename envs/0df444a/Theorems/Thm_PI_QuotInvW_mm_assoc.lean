-- Prove2me | Theorems.Thm_PI_QuotInvW_mm_assoc
-- name    : PI.QuotInvW.mm_assoc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:30:32.377698+00:00
-- url     : https://prove2.me/theorems/2315c796-bb2d-4d35-9925-c2c5bcfbdc30
-- title:
--   Quot Inv W: mm assoc
-- statement:
--   The Quot Inv W construction uses the mm assoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientInvariantMeasurability/MeasurableMmRight.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientInvariantMeasurability/MeasurableMmRight.lean#L39-L42

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

theorem PI.QuotInvW.mm_assoc (a b c : MtM m) : mm (mm a b) c = mm a (mm b c) := by sorry
