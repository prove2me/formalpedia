-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CompactEntryBounds_Kset_compact
-- name    : ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds.Kset_compact
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:19:20.669062+00:00
-- url     : https://prove2.me/theorems/bcb9f4fd-2382-4641-9df3-6ea68c1fc547
-- title:
--   Compact Entry Bounds: Kset compact
-- statement:
--   The Compact Entry Bounds construction uses the Kset compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CompactEntryBounds.lean#L166-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CompactEntryBounds.lean#L166-L183

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralBasisReduction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CompactEntryBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds
open Matrix NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds.Kset_compact (R : ℝ) : IsCompact (Kset X R) := by sorry
