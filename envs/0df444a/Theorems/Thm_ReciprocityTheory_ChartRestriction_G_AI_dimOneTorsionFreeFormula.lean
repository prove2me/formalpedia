-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_dimOneTorsionFreeFormula
-- name    : ReciprocityTheory.ChartRestriction.G.AI.dimOneTorsionFreeFormula
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:55.651597+00:00
-- url     : https://prove2.me/theorems/5cf52562-316f-43b5-b1a2-5503cadf02cd
-- title:
--   AI: dim One Torsion Free Formula
-- statement:
--   The AI construction uses the dim One Torsion Free Formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/KrullDimQuotientEqOneIffEqBot.lean#L111-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/KrullDimQuotientEqOneIffEqBot.lean#L111-L129

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KrullDimQuotientEqOneIffEqBot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module

theorem ReciprocityTheory.ChartRestriction.G.AI.dimOneTorsionFreeFormula : LocalLengthAdditivityTorsionFree := by sorry
