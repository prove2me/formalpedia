-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hups_uDeg_eq
-- name    : ReciprocityTheory.ChartRestriction.G.T0.hups_uDeg_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T06:12:51.826795+00:00
-- url     : https://prove2.me/theorems/d6a4ea9b-7846-427f-9797-c51b721ef959
-- title:
--   T0: hups u Deg eq
-- statement:
--   The T0 construction uses the hups u Deg eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/PolyL2EqSqrtCoeffSum.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/PolyL2EqSqrtCoeffSum.lean#L19-L22

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsTwCoeffCoeff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_MinkSat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SatDegLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsChooseRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PolyL2EqSqrtCoeffSum
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

theorem ReciprocityTheory.ChartRestriction.G.T0.hups_uDeg_eq {D N : ℕ} (s : UXVar D N →₀ ℕ) : uDeg s = hupsWt (hupsWu D N) s := by sorry
