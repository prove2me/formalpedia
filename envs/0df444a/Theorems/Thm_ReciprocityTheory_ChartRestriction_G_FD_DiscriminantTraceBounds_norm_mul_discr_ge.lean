-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DiscriminantTraceBounds_norm_mul_discr_ge
-- name    : ReciprocityTheory.ChartRestriction.G.FD.DiscriminantTraceBounds.norm_mul_discr_ge
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:16:45.303921+00:00
-- url     : https://prove2.me/theorems/13555090-30a4-5efe-b2c0-78c6ee943aed
-- title:
--   Discriminant Trace Bounds: norm mul discr ge
-- statement:
--   The Discriminant Trace Bounds construction uses the norm mul discr ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/DiscriminantTraceBounds.lean#L12-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/DiscriminantTraceBounds.lean#L12-L64

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscriminantTraceBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.DiscriminantTraceBounds
open NumberField Complex Module Matrix
open scoped ComplexConjugate nonZeroDivisors
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.ChartRestriction.G.FD.DiscriminantTraceBounds.norm_mul_discr_ge {x : E} (hx : x ≠ 0)
    (htr : ∀ β : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (x * β) = m) :
    1 ≤ |Algebra.norm ℚ x| * |(NumberField.discr E : ℚ)| := by sorry
