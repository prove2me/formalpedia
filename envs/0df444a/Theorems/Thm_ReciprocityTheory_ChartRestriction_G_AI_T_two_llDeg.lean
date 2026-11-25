-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_T_two_llDeg
-- name    : ReciprocityTheory.ChartRestriction.G.AI.T.two_llDeg
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:55:39.596555+00:00
-- url     : https://prove2.me/theorems/0530287d-c370-51f4-ad87-22ffd2bef6e3
-- title:
--   T: two ll Deg
-- statement:
--   The T construction uses the two ll Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/DiagonalDivisors/InhabitBaseStatement.lean#L139-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/DiagonalDivisors/InhabitBaseStatement.lean#L139-L141

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

theorem ReciprocityTheory.ChartRestriction.G.AI.T.two_llDeg : 2 • llDeg = -(twoXiDeg 0 + twoXiDeg 1) := by sorry
