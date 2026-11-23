-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hint_fubini
-- name    : ReciprocityTheory.ChartRestriction.G.T0.hint_fubini
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:57.556116+00:00
-- url     : https://prove2.me/theorems/45cece06-5a96-4e61-bbc7-698944b987ea
-- title:
--   T0: hint fubini
-- statement:
--   The T0 construction uses the hint fubini property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HintIntOfBounds.lean#L135-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HintIntOfBounds.lean#L135-L152

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

theorem ReciprocityTheory.ChartRestriction.G.T0.hint_fubini {D n : ℕ} (hn : 0 < n) {a : Fin (D + 1) → ℕ}
    {F : MvPolynomial (Fin (D + 1) × Fin n) ℂ} (hF0 : F ≠ 0) (hF : IsMultiHomogeneous a F) :
    Integrable (fun z : BlockSphere D n =>
      ∫ s, Real.log ‖MvPolynomial.eval (hintPt (spherePoint s) z) F‖ ∂(sphereProb n))
      (blockSphereProb D n) := by sorry
