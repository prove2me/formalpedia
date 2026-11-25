-- Prove2me | Theorems.Thm_PI_FoldMult_UnitaryGroupMassFormula_isClosed_hitSet
-- name    : PI.FoldMult.UnitaryGroupMassFormula.isClosed_hitSet
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:31:00.458288+00:00
-- url     : https://prove2.me/theorems/49f3a72d-09ed-50dc-bd61-aa104b97ba71
-- title:
--   Unitary Group Mass Formula: is Closed hit Set
-- statement:
--   The Unitary Group Mass Formula construction uses the is Closed hit Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MultiplicityMeasurability/MeasurableMult.lean#L64-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MultiplicityMeasurability/MeasurableMult.lean#L64-L89

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

theorem PI.FoldMult.UnitaryGroupMassFormula.isClosed_hitSet (Γ : Subgroup G) (Ω : Set G) (hΩ : IsCompact Ω) (A : Finset Γ) :
    IsClosed (hitSet Γ Ω A) := by sorry
