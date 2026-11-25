-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_shortVectorBound
-- name    : ReciprocityTheory.ChartRestriction.G.FD.shortVectorBound
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:14:48.859626+00:00
-- url     : https://prove2.me/theorems/7615a00d-55a7-56dd-bea9-0c18b8adb7c5
-- title:
--   FD: short Vector Bound
-- statement:
--   The FD construction uses the short Vector Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ShortVectorBound.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ShortVectorBound.lean#L8-L9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ShortVectorBoundOfCoefficientBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ShortVectorSixthLemmaPrimeHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ShortVectorBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.FD.shortVectorBound : ShortVectorBound (E := E) := by sorry
