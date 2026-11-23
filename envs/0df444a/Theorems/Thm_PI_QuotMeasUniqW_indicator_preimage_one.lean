-- Prove2me | Theorems.Thm_PI_QuotMeasUniqW_indicator_preimage_one
-- name    : PI.QuotMeasUniqW.indicator_preimage_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:39:30.846735+00:00
-- url     : https://prove2.me/theorems/aa5e0755-9a9f-498d-ac85-28865066c89e
-- title:
--   Quot Meas Uniq W: indicator preimage one
-- statement:
--   The Quot Meas Uniq W construction uses the indicator preimage one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientMeasureUniqueness/QLiftIsMulLeftInvariant.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientMeasureUniqueness/QLiftIsMulLeftInvariant.lean#L11-L16

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QmuWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QLiftIsMulLeftInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Pointwise
open scoped ENNReal
open PI PI.QuotMeasUniqW

theorem PI.QuotMeasUniqW.indicator_preimage_one {α β : Type*} (f : α → β) (s : Set β) (x : α) :
    (f ⁻¹' s).indicator (1 : α → ℝ≥0∞) x = s.indicator 1 (f x) := by sorry
