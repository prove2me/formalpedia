-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hint_logInt_tail
-- name    : ReciprocityTheory.ChartRestriction.G.T0.hint_logInt_tail
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:31.603809+00:00
-- url     : https://prove2.me/theorems/0090ff40-0f88-446c-adcb-148c1d02df4c
-- title:
--   T0: hint log Int tail
-- statement:
--   The T0 construction uses the hint log Int tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HintIntOfBounds.lean#L95-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HintIntOfBounds.lean#L95-L112

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

theorem ReciprocityTheory.ChartRestriction.G.T0.hint_logInt_tail {D n : ℕ} (hn : 0 < n) {a : Fin (D + 1) → ℕ}
    {q : MvPolynomial (Fin (D + 1) × Fin n) ℂ} (hq0 : q ≠ 0) (hq : IsMultiHomogeneous a q)
    (ha : a 0 = 0) (t0 : Fin n → ℂ) :
    Integrable (fun z : BlockSphere D n => Real.log ‖MvPolynomial.eval (hintPt t0 z) q‖)
      (blockSphereProb D n) := by sorry
