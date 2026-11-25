-- Prove2me | Theorems.Thm_PI_QuotMeasUniqW_qLift_finite
-- name    : PI.QuotMeasUniqW.qLift_finite
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:18:30.629566+00:00
-- url     : https://prove2.me/theorems/c88fc9e9-e722-502b-88ab-984b4b86df6e
-- title:
--   Quot Meas Uniq W: q Lift finite
-- statement:
--   The Quot Meas Uniq W construction uses the q Lift finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientMeasureUniqueness/QLiftIsMulLeftInvariant.lean#L169-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientMeasureUniqueness/QLiftIsMulLeftInvariant.lean#L169-L211

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

theorem PI.QuotMeasUniqW.qLift_finite {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}
    (hH : IsClosed (H : Set G)) (ν : Measure H) [SFinite ν] [ν.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts ν] (ρ : Measure (G ⧸ H))
    (hρK : ∀ K : Set (G ⧸ H), IsCompact K → ρ K < ⊤) : IsFiniteMeasureOnCompacts (qLift ν ρ) := by sorry
