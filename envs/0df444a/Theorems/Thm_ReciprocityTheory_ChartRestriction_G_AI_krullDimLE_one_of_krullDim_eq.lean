-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_krullDimLE_one_of_krullDim_eq
-- name    : ReciprocityTheory.ChartRestriction.G.AI.krullDimLE_one_of_krullDim_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:46.936333+00:00
-- url     : https://prove2.me/theorems/163223b9-8601-41a4-8821-495a1e227906
-- title:
--   AI: krull Dim LE one of krull Dim eq
-- statement:
--   The AI construction uses the krull Dim LE one of krull Dim eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/KrullDimQuotientEqOneIffEqBot.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/KrullDimQuotientEqOneIffEqBot.lean#L10-L12

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
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]

theorem ReciprocityTheory.ChartRestriction.G.AI.krullDimLE_one_of_krullDim_eq (h : ringKrullDim A = 1) : Ring.KrullDimLE 1 A := by sorry
