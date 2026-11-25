-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_p2_mem_Z2_of_mem_Z2
-- name    : ReciprocityTheory.ChartRestriction.G.I2.Col.p2_mem_Z2_of_mem_Z2
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:27:05.256872+00:00
-- url     : https://prove2.me/theorems/e5ce8f3b-d76c-444b-a1ad-e7026d6bbcc4
-- title:
--   Col: p2 mem Z2 of mem Z2
-- statement:
--   The Col construction uses the p2 mem Z2 of mem Z2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SecondProjectionOrthogonalComplement.lean#L232-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SecondProjectionOrthogonalComplement.lean#L232-L243

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

theorem ReciprocityTheory.ChartRestriction.G.I2.Col.p2_mem_Z2_of_mem_Z2 (v : EuclideanSpace ℂ ι) : p2 K v ∈ V2 K := by sorry
