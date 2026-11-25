-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_GelfCpt_integrable_of_continuous_cpt
-- name    : PI.UnitaryGroupMassFormula.GelfCpt.integrable_of_continuous_cpt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:38:12.200249+00:00
-- url     : https://prove2.me/theorems/ddceea9f-fd86-5998-96e9-8c219bb1fda3
-- title:
--   Gelf Cpt: integrable of continuous cpt
-- statement:
--   The Gelf Cpt construction uses the integrable of continuous cpt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGelfandAverage/IntegrableOfContinuousCpt.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGelfandAverage/IntegrableOfContinuousCpt.lean#L11-L14

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_AvgStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_IntegrableOfContinuousCpt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.GelfCpt
open MeasureTheory Matrix

theorem PI.UnitaryGroupMassFormula.GelfCpt.integrable_of_continuous_cpt {X : Type} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    {F : X → ℂ} (hF : Continuous F) : Integrable F ν := by sorry
