-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_cab_contDiff_top
-- name    : ReciprocityTheory.ChartRestriction.G.I2.cab_contDiff_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:16.980558+00:00
-- url     : https://prove2.me/theorems/db19a2c8-57e9-49bb-a4ef-0e3f5fbd1b98
-- title:
--   I2: cab cont Diff top
-- statement:
--   The I2 construction uses the cab cont Diff top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColAbelA.lean#L130-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColAbelA.lean#L130-L138

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColAbelA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.I2.cab_contDiff_top {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {F : W → ℂ} (hF : Differentiable ℂ F) : ContDiff ℂ (⊤ : WithTop ℕ∞) F := by sorry
