-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_Hf_rsmul_r
-- name    : ReciprocityTheory.ChartRestriction.G.I2.Col.Hf_rsmul_r
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:38.363797+00:00
-- url     : https://prove2.me/theorems/d357796e-c138-4b18-bf4c-dffa91be51f8
-- title:
--   Col: Hf rsmul r
-- statement:
--   The Col construction uses the Hf rsmul r property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SecondProjectionOrthogonalComplement.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SecondProjectionOrthogonalComplement.lean#L33-L35

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

theorem ReciprocityTheory.ChartRestriction.G.I2.Col.Hf_rsmul_r (r : ℝ) (v w : EuclideanSpace ℂ ι) : Hf v (r • w) = r * Hf v w := by sorry
