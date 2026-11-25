-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_isMH_mul_X
-- name    : ReciprocityTheory.ChartRestriction.G.T0.NPB.isMH_mul_X
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:37:38.746552+00:00
-- url     : https://prove2.me/theorems/bf5ebf63-7de2-545a-9c25-23c5cb4a6e1b
-- title:
--   NPB: is MH mul X
-- statement:
--   The NPB construction uses the is MH mul X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CastAddNeNatAdd.lean#L28-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CastAddNeNatAdd.lean#L28-L40

import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CastAddNeNatAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.NPB
open MvPolynomial MeasureTheory ReciprocityTheory.MultiplicativeHeights
variable {R : Type*} [CommSemiring R] {B n : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.T0.NPB.isMH_mul_X {a : Fin B → ℕ} {f : MvPolynomial (Fin B × Fin n) R}
    (hf : IsMultiHomogeneous a f) (i : Fin B) (j : Fin n) :
    IsMultiHomogeneous (a + Pi.single i 1) (f * X (i, j)) := by sorry
