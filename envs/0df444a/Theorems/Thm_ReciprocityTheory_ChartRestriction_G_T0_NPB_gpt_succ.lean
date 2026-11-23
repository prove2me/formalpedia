-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_succ
-- name    : ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:26.379799+00:00
-- url     : https://prove2.me/theorems/c51769ab-aacc-413f-9232-172628c9e819
-- title:
--   NPB: gpt succ
-- statement:
--   The NPB construction uses the gpt succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CastAddNeNatAdd.lean#L149-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CastAddNeNatAdd.lean#L149-L150

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

theorem ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_succ (tt : Fin D × Fin (N + 1) → ℂ) (y : Fin (N + 1 + D) → ℂ) (i : Fin D)
    (j : Fin (N + 1)) : gpt tt y (i.succ, j) = y (Fin.natAdd (N + 1) i) * tt (i, j) := by sorry
