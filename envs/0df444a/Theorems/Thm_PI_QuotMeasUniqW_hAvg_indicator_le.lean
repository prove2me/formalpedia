-- Prove2me | Theorems.Thm_PI_QuotMeasUniqW_hAvg_indicator_le
-- name    : PI.QuotMeasUniqW.hAvg_indicator_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:39:18.342372+00:00
-- url     : https://prove2.me/theorems/a09e6caa-89fc-4f4f-87d2-8bf3efc1dcb8
-- title:
--   Quot Meas Uniq W: h Avg indicator le
-- statement:
--   The Quot Meas Uniq W construction uses the h Avg indicator le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientMeasureUniqueness/QLiftIsMulLeftInvariant.lean#L61-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientMeasureUniqueness/QLiftIsMulLeftInvariant.lean#L61-L85

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

theorem PI.QuotMeasUniqW.hAvg_indicator_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}
    (ν : Measure H) [ν.IsMulLeftInvariant] (C K : Set G) (d g : G) (hC : ∀ x ∈ C, d⁻¹ * x ∈ K) :
    hAvg ν (C.indicator 1) g ≤ ν {h : H | (h : G) ∈ K⁻¹ * K} := by sorry
