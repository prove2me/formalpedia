-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_herm_proj_one_one
-- name    : ReciprocityTheory.ChartRestriction.G.I2.Col.herm_proj_one_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:26:28.832477+00:00
-- url     : https://prove2.me/theorems/2aec3907-72b5-449a-8667-99222a92a22b
-- title:
--   Col: herm proj one one
-- statement:
--   The Col construction uses the herm proj one one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SecondProjectionOrthogonalComplement.lean#L136-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SecondProjectionOrthogonalComplement.lean#L136-L140

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

theorem ReciprocityTheory.ChartRestriction.G.I2.Col.herm_proj_one_one (v w : EuclideanSpace ℂ ι) :
    Hf (p1 K v) (p1 K w) = ∑ k, z K k v * (starRingEnd ℂ) (z K k w) := by sorry
