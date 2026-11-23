-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hint_eval_indep
-- name    : ReciprocityTheory.ChartRestriction.G.T0.hint_eval_indep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:50:44.285833+00:00
-- url     : https://prove2.me/theorems/c74a0c69-e274-45ca-be03-4dd1fa7c0538
-- title:
--   T0: hint eval indep
-- statement:
--   The T0 construction uses the hint eval indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HintIntOfBounds.lean#L60-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HintIntOfBounds.lean#L60-L80

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

theorem ReciprocityTheory.ChartRestriction.G.T0.hint_eval_indep {D n : ℕ} {a : Fin (D + 1) → ℕ} {q : MvPolynomial (Fin (D + 1) × Fin n) ℂ}
    (hq : IsMultiHomogeneous a q) (ha : a 0 = 0) (x y : Fin (D + 1) × Fin n → ℂ)
    (hxy : ∀ v : Fin (D + 1) × Fin n, v.1 ≠ 0 → x v = y v) :
    MvPolynomial.eval x q = MvPolynomial.eval y q := by sorry
