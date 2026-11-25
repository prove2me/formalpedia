-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_normSq_sub_le_two
-- name    : ReciprocityTheory.ChartRestriction.G.FD.normSq_sub_le_two
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:22:00.622483+00:00
-- url     : https://prove2.me/theorems/b3d83aa5-cd6e-4641-b98c-5d7c2f5d862a
-- title:
--   FD: norm Sq sub le two
-- statement:
--   The FD construction uses the norm Sq sub le two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentSubOneMajorantBound.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentSubOneMajorantBound.lean#L10-L13

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentOnHyperbolicComplement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentSubOneMajorantBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.FD.normSq_sub_le_two (a b : ℂ) :
    Complex.normSq (a - b) ≤ 2 * Complex.normSq a + 2 * Complex.normSq b := by sorry
