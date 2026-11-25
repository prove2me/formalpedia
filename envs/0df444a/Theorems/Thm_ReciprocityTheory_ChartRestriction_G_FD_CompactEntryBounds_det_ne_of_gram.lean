-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CompactEntryBounds_det_ne_of_gram
-- name    : ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds.det_ne_of_gram
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:17:01.205596+00:00
-- url     : https://prove2.me/theorems/45875d55-376c-4131-b81d-f20c6709a236
-- title:
--   Compact Entry Bounds: det ne of gram
-- statement:
--   The Compact Entry Bounds construction uses the det ne of gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CompactEntryBounds.lean#L185-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CompactEntryBounds.lean#L185-L194

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

theorem ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds.det_ne_of_gram {τ : E →+* ℂ} {Y : Matrix (Fin r) (Fin r) ℂ} {p0 : ℕ}
    (hg : gram τ X.Gm Y = diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) : Y.det ≠ 0 := by sorry
