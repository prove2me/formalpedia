-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_starProj_eq
-- name    : ReciprocityTheory.ChartRestriction.G.I2.Col.starProj_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:26:57.439872+00:00
-- url     : https://prove2.me/theorems/c52ac629-b2cd-47a6-bf88-19d156a8f5e5
-- title:
--   Col: star Proj eq
-- statement:
--   The Col construction uses the star Proj eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SecondProjectionOrthogonalComplement.lean#L245-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SecondProjectionOrthogonalComplement.lean#L245-L253

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

theorem ReciprocityTheory.ChartRestriction.G.I2.Col.starProj_eq (v : EuclideanSpace ℂ ι) : (V2 K).starProjection v = p2 K v := by sorry
