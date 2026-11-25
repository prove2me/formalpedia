-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DiscriminantTraceBounds_two_le_normSq_mul_rootDisc
-- name    : ReciprocityTheory.ChartRestriction.G.FD.DiscriminantTraceBounds.two_le_normSq_mul_rootDisc
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:13:29.675704+00:00
-- url     : https://prove2.me/theorems/48f343ff-3c18-4ee4-848d-232816bff597
-- title:
--   Discriminant Trace Bounds: two le norm Sq mul root Disc
-- statement:
--   The Discriminant Trace Bounds construction uses the two le norm Sq mul root Disc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/DiscriminantTraceBounds.lean#L269-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/DiscriminantTraceBounds.lean#L269-L309

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
variable [IsCMField E] {r : ℕ} (X : DataX E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.DiscriminantTraceBounds.two_le_normSq_mul_rootDisc (hr : 0 < r) : 2 ≤ (X.NC : ℝ) ^ 2 * X.k0 * rdE E := by sorry
