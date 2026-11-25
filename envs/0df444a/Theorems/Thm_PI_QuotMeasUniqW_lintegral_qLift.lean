-- Prove2me | Theorems.Thm_PI_QuotMeasUniqW_lintegral_qLift
-- name    : PI.QuotMeasUniqW.lintegral_qLift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:58:14.331594+00:00
-- url     : https://prove2.me/theorems/584587db-cbd7-4600-b485-86bd14419b4d
-- title:
--   Quot Meas Uniq W: lintegral q Lift
-- statement:
--   The Quot Meas Uniq W construction uses the lintegral q Lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientMeasureUniqueness/QLiftIsMulLeftInvariant.lean#L113-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientMeasureUniqueness/QLiftIsMulLeftInvariant.lean#L113-L120

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

theorem PI.QuotMeasUniqW.lintegral_qLift {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}
    (ν : Measure H) [SFinite ν] [ν.IsMulLeftInvariant] (ρ : Measure (G ⧸ H)) {f : G → ℝ≥0∞}
    (hf : Measurable f) : ∫⁻ x, f x ∂qLift ν ρ = ∫⁻ y, hAvg ν f y.out ∂ρ := by sorry
