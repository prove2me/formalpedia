-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_untopD_nonneg
-- name    : ReciprocityTheory.ChartRestriction.G.T0.untopD_nonneg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:13:43.962711+00:00
-- url     : https://prove2.me/theorems/18de3fc8-ddcc-596f-a849-b62e6ec92e84
-- title:
--   T0: untop D nonneg
-- statement:
--   The T0 construction uses the untop D nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GeneratorNeZeroOfHeight.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GeneratorNeZeroOfHeight.lean#L21-L24

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField

theorem ReciprocityTheory.ChartRestriction.G.T0.untopD_nonneg {x : WithTop ℤ} (hx : 0 ≤ x) : 0 ≤ WithTop.untopD 0 x := by sorry
