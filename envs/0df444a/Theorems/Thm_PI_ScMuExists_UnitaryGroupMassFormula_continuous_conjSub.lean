-- Prove2me | Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_continuous_conjSub
-- name    : PI.ScMuExists.UnitaryGroupMassFormula.continuous_conjSub
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:40:58.454282+00:00
-- url     : https://prove2.me/theorems/6529ec3a-2f22-5f14-8fde-0ca16fdc1c85
-- title:
--   Unitary Group Mass Formula: continuous conj Sub
-- statement:
--   The Unitary Group Mass Formula construction uses the continuous conj Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/ModOne.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/ModOne.lean#L23-L26

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ModOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal Pointwise
noncomputable section
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem PI.ScMuExists.UnitaryGroupMassFormula.continuous_conjSub (N : Subgroup G) (g : G) (h1 : ∀ x ∈ N, g * x * g⁻¹ ∈ N)
    (h2 : ∀ x ∈ N, g⁻¹ * x * g ∈ N) : Continuous (conjSub N g h1 h2) := by sorry
