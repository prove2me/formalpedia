-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_zero
-- name    : ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:16.932138+00:00
-- url     : https://prove2.me/theorems/9425938e-8e1e-4549-a910-e906dedb6576
-- title:
--   NPB: h Img zero
-- statement:
--   The NPB construction uses the h Img zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CastAddNeNatAdd.lean#L62-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CastAddNeNatAdd.lean#L62-L64

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
variable {K : Type} [Field K] {D N : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_zero (j : Fin (N + 1)) :
    hImg (K := K) (D := D) ((0 : Fin (D + 1)), j) = X (Fin.castAdd D j) := by sorry
