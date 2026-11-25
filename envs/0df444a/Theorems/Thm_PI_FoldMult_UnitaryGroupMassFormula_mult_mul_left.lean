-- Prove2me | Theorems.Thm_PI_FoldMult_UnitaryGroupMassFormula_mult_mul_left
-- name    : PI.FoldMult.UnitaryGroupMassFormula.mult_mul_left
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:30:48.874436+00:00
-- url     : https://prove2.me/theorems/18249c02-b878-4f6c-a4f6-a4176b98ce15
-- title:
--   Unitary Group Mass Formula: mult mul left
-- statement:
--   The Unitary Group Mass Formula construction uses the mult mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MultiplicityMeasurability/MeasurableMult.lean#L45-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MultiplicityMeasurability/MeasurableMult.lean#L45-L59

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

theorem PI.FoldMult.UnitaryGroupMassFormula.mult_mul_left (Γ : Subgroup G) (Ω : Set G) (γ : G) (hγ : γ ∈ Γ) (x : G) :
    Formalism.L2.SG.FoldBound.mult Γ Ω (γ * x) = Formalism.L2.SG.FoldBound.mult Γ Ω x := by sorry
