-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_Hf_rsmul_l
-- name    : ReciprocityTheory.ChartRestriction.G.I2.Col.Hf_rsmul_l
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:26:17.285664+00:00
-- url     : https://prove2.me/theorems/be6843b1-e9ea-5aa7-8e98-1c6958d364bd
-- title:
--   Col: Hf rsmul l
-- statement:
--   The Col construction uses the Hf rsmul l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SecondProjectionOrthogonalComplement.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SecondProjectionOrthogonalComplement.lean#L37-L39

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

theorem ReciprocityTheory.ChartRestriction.G.I2.Col.Hf_rsmul_l (r : ℝ) (v w : EuclideanSpace ℂ ι) : Hf (r • v) w = r * Hf v w := by sorry
