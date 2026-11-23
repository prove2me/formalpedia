-- Prove2me | Theorems.Thm_PI_QuotMeasUniqW_lintegral_qKer
-- name    : PI.QuotMeasUniqW.lintegral_qKer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:39:20.94428+00:00
-- url     : https://prove2.me/theorems/6c6da108-ae3a-4d7a-a4a8-f975dea2cb6a
-- title:
--   Quot Meas Uniq W: lintegral q Ker
-- statement:
--   The Quot Meas Uniq W construction uses the lintegral q Ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientMeasureUniqueness/QLiftIsMulLeftInvariant.lean#L91-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientMeasureUniqueness/QLiftIsMulLeftInvariant.lean#L91-L95

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

theorem PI.QuotMeasUniqW.lintegral_qKer {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] {H : Subgroup G} (ν : Measure H) {f : G → ℝ≥0∞}
    (hf : Measurable f) (y : G ⧸ H) : ∫⁻ x, f x ∂qKer ν y = hAvg ν f y.out := by sorry
