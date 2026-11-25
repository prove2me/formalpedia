-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CompactEntryBounds_Kset_sub
-- name    : ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds.Kset_sub
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:19:55.256797+00:00
-- url     : https://prove2.me/theorems/05f07316-0f9b-481a-b3f7-8c757e4b6467
-- title:
--   Compact Entry Bounds: Kset sub
-- statement:
--   The Compact Entry Bounds construction uses the Kset sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CompactEntryBounds.lean#L196-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CompactEntryBounds.lean#L196-L209

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

theorem ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds.Kset_sub (R : ℝ) : Kset X R ⊆ X.dom := by sorry
