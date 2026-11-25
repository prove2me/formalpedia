-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_herm_proj_one_two
-- name    : ReciprocityTheory.ChartRestriction.G.I2.Col.herm_proj_one_two
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:26:31.928278+00:00
-- url     : https://prove2.me/theorems/0e4a330a-fe77-41ba-b5b8-f6a1bf8247a9
-- title:
--   Col: herm proj one two
-- statement:
--   The Col construction uses the herm proj one two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SecondProjectionOrthogonalComplement.lean#L133-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SecondProjectionOrthogonalComplement.lean#L133-L134

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
open scoped InnerProductSpace
noncomputable section
open ReciprocityTheory.ChartRestriction.G.I2.Col
variable {ι : Type} [Fintype ι]
variable (K : Submodule ℝ (EuclideanSpace ℂ ι))
variable {K}
variable (hK : ∀ a ∈ K, ∀ b ∈ K, (Hf a b).im = 0)
include hK

theorem ReciprocityTheory.ChartRestriction.G.I2.Col.herm_proj_one_two (v w : EuclideanSpace ℂ ι) : Hf (p1 K v) (p2 K w) = 0 := by sorry
