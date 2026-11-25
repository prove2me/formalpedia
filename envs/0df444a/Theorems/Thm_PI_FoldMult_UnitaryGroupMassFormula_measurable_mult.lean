-- Prove2me | Theorems.Thm_PI_FoldMult_UnitaryGroupMassFormula_measurable_mult
-- name    : PI.FoldMult.UnitaryGroupMassFormula.measurable_mult
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:31:06.554405+00:00
-- url     : https://prove2.me/theorems/dab0e927-aa2b-5e99-b052-a10c4fa58650
-- title:
--   Unitary Group Mass Formula: measurable mult
-- statement:
--   The Unitary Group Mass Formula construction uses the measurable mult property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MultiplicityMeasurability/MeasurableMult.lean#L118-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MultiplicityMeasurability/MeasurableMult.lean#L118-L126

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FoldMult
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MultiplicityMeasurability_MeasurableMult
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal
open PI PI.FoldMult PI.FoldMult.UnitaryGroupMassFormula
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

theorem PI.FoldMult.UnitaryGroupMassFormula.measurable_mult [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] (Ω : Set G) (hΩ : IsCompact Ω) :
    Measurable (Formalism.L2.SG.FoldBound.mult Γ Ω) := by sorry
