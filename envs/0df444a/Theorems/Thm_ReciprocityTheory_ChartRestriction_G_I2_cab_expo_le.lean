-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_cab_expo_le
-- name    : ReciprocityTheory.ChartRestriction.G.I2.cab_expo_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:28:46.382298+00:00
-- url     : https://prove2.me/theorems/8faeba40-5e48-4db3-ac66-33fadec3e85f
-- title:
--   I2: cab expo le
-- statement:
--   The I2 construction uses the cab expo le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColAbelA.lean#L169-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColAbelA.lean#L169-L174

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

theorem ReciprocityTheory.ChartRestriction.G.I2.cab_expo_le {q t u c : ℝ} (hq : 0 < q) (hqt : q * t ^ 2 ≤ c) :
    q * Real.pi * t ^ 2 / 2 - q * Real.pi * u ^ 2 + 2 * q * Real.pi * t * u ≤
      5 * Real.pi * c / 2 - Real.pi / 2 * q * u ^ 2 := by sorry
