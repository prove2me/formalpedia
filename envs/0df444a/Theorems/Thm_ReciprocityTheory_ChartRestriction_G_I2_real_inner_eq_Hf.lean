-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_real_inner_eq_Hf
-- name    : ReciprocityTheory.ChartRestriction.G.I2.real_inner_eq_Hf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:40.362526+00:00
-- url     : https://prove2.me/theorems/98cc1727-6f6f-48ed-9d36-6599ba94a9ad
-- title:
--   I2: real inner eq Hf
-- statement:
--   The I2 construction uses the real inner eq Hf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitA.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitA.lean#L30-L31

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
variable {ι : Type} [Fintype ι]

theorem ReciprocityTheory.ChartRestriction.G.I2.real_inner_eq_Hf (x y : EuclideanSpace ℂ ι) : ⟪x, y⟫_ℝ = (Hf y x).re := by sorry
