-- Prove2me | Theorems.Thm_PI_QuotMeasUniqW_hAvg_mul_mem
-- name    : PI.QuotMeasUniqW.hAvg_mul_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:18:12.933135+00:00
-- url     : https://prove2.me/theorems/7f966d87-1b51-510c-ac90-7d63fa4bfd77
-- title:
--   Quot Meas Uniq W: h Avg mul mem
-- statement:
--   The Quot Meas Uniq W construction uses the h Avg mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientMeasureUniqueness/QLiftIsMulLeftInvariant.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientMeasureUniqueness/QLiftIsMulLeftInvariant.lean#L30-L35

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

theorem PI.QuotMeasUniqW.hAvg_mul_mem {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}
    (ν : Measure H) [ν.IsMulLeftInvariant] (f : G → ℝ≥0∞) (g : G) (h0 : H) :
    hAvg ν f (g * h0) = hAvg ν f g := by sorry
