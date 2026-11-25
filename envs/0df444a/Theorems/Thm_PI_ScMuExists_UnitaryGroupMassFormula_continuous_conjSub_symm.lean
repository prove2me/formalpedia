-- Prove2me | Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_continuous_conjSub_symm
-- name    : PI.ScMuExists.UnitaryGroupMassFormula.continuous_conjSub_symm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:41:05.530831+00:00
-- url     : https://prove2.me/theorems/1733dd92-1fb4-5dd3-8b1c-9a4dfc68fe35
-- title:
--   Unitary Group Mass Formula: continuous conj Sub symm
-- statement:
--   The Unitary Group Mass Formula construction uses the continuous conj Sub symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/ModOne.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/ModOne.lean#L28-L31

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

theorem PI.ScMuExists.UnitaryGroupMassFormula.continuous_conjSub_symm (N : Subgroup G) (g : G) (h1 : ∀ x ∈ N, g * x * g⁻¹ ∈ N)
    (h2 : ∀ x ∈ N, g⁻¹ * x * g ∈ N) : Continuous (conjSub N g h1 h2).symm := by sorry
