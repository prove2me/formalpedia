-- Prove2me | Theorems.Thm_PI_FoldMult_UnitaryGroupMassFormula_cnt_encard_le
-- name    : PI.FoldMult.UnitaryGroupMassFormula.cnt_encard_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:02.077902+00:00
-- url     : https://prove2.me/theorems/c1ef908e-cfb9-41f4-97ba-f2df95c0dc0d
-- title:
--   Unitary Group Mass Formula: cnt encard le
-- statement:
--   The Unitary Group Mass Formula construction uses the cnt encard le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MultiplicityMeasurability/MeasurableMult.lean#L13-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MultiplicityMeasurability/MeasurableMult.lean#L13-L29

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

theorem PI.FoldMult.UnitaryGroupMassFormula.cnt_encard_le (Γ : Subgroup G) [DiscreteTopology Γ] (Ω : Set G) (hΩ : IsCompact Ω)
    (x : G) : ∃ N : ℕ∞, N < ⊤ ∧ ∀ y, (cnt Γ Ω x y).encard ≤ N := by sorry
