-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_T_pullDeg_twoXiDegY
-- name    : ReciprocityTheory.ChartRestriction.G.AI.T.pullDeg_twoXiDegY
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:10:58.404317+00:00
-- url     : https://prove2.me/theorems/0fedc331-e06d-4998-9c81-053d61e458ac
-- title:
--   T: pull Deg two Xi Deg Y
-- statement:
--   The T construction uses the pull Deg two Xi Deg Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/DiagonalDivisors/InhabitBaseStatement.lean#L158-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/DiagonalDivisors/InhabitBaseStatement.lean#L158-L160

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_DiagonalDivisors_ModelsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_DiagonalDivisors_InhabitBaseStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.T
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
universe u

theorem ReciprocityTheory.ChartRestriction.G.AI.T.pullDeg_twoXiDegY (j : Fin 2) : pullDeg j twoXiDegY = twoXiDeg j := by sorry
