-- Prove2me | Theorems.Thm_PI_FoldMult_UnitaryGroupMassFormula_mult_lt_top
-- name    : PI.FoldMult.UnitaryGroupMassFormula.mult_lt_top
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:27.499451+00:00
-- url     : https://prove2.me/theorems/53c3ca9c-428d-43ed-a52f-cdd667dc2624
-- title:
--   Unitary Group Mass Formula: mult lt top
-- statement:
--   The Unitary Group Mass Formula construction uses the mult lt top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MultiplicityMeasurability/MeasurableMult.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MultiplicityMeasurability/MeasurableMult.lean#L39-L43

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

theorem PI.FoldMult.UnitaryGroupMassFormula.mult_lt_top (Γ : Subgroup G) [DiscreteTopology Γ] (Ω : Set G) (hΩ : IsCompact Ω)
    (x : G) : Formalism.L2.SG.FoldBound.mult Γ Ω x < ⊤ := by sorry
