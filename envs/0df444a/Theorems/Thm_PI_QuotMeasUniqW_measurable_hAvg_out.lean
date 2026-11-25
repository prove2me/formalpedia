-- Prove2me | Theorems.Thm_PI_QuotMeasUniqW_measurable_hAvg_out
-- name    : PI.QuotMeasUniqW.measurable_hAvg_out
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:39:37.096847+00:00
-- url     : https://prove2.me/theorems/44c49a8b-6d0f-455c-9fba-de3cd18b3eca
-- title:
--   Quot Meas Uniq W: measurable h Avg out
-- statement:
--   The Quot Meas Uniq W construction uses the measurable h Avg out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientMeasureUniqueness/QLiftIsMulLeftInvariant.lean#L48-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientMeasureUniqueness/QLiftIsMulLeftInvariant.lean#L48-L55

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

theorem PI.QuotMeasUniqW.measurable_hAvg_out {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}
    (ν : Measure H) [SFinite ν] [ν.IsMulLeftInvariant] {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun y : G ⧸ H => hAvg ν f y.out) := by sorry
