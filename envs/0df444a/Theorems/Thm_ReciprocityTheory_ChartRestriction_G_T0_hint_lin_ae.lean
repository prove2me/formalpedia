-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hint_lin_ae
-- name    : ReciprocityTheory.ChartRestriction.G.T0.hint_lin_ae
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:41.198232+00:00
-- url     : https://prove2.me/theorems/a9caadf1-0d7c-4103-bb81-2d527f24bc37
-- title:
--   T0: hint lin ae
-- statement:
--   The T0 construction uses the hint lin ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HintIntOfBounds.lean#L154-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HintIntOfBounds.lean#L154-L186

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntCoresA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintIntOfBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MeasureTheory ReciprocityTheory.MultiplicativeHeights

theorem ReciprocityTheory.ChartRestriction.G.T0.hint_lin_ae {n : ℕ} (c : Fin n → ℂ) (hc : c ≠ 0) :
    ∀ᵐ s ∂(sphereProb n), ∑ j, c j * spherePoint s j ≠ 0 := by sorry
