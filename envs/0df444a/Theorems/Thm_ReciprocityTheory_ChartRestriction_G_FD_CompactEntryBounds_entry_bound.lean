-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CompactEntryBounds_entry_bound
-- name    : ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds.entry_bound
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:18:43.9795+00:00
-- url     : https://prove2.me/theorems/f535ae0e-e890-5fbd-99f4-22c87b5e0d04
-- title:
--   Compact Entry Bounds: entry bound
-- statement:
--   The Compact Entry Bounds construction uses the entry bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CompactEntryBounds.lean#L77-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CompactEntryBounds.lean#L77-L116

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

theorem ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds.entry_bound {τ : E →+* ℂ} {Y : Matrix (Fin r) (Fin r) ℂ} (hY : Y.det ≠ 0)
    (hg : gram τ X.Gm Y = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (l b : Fin r) :
    ‖Y l b‖ ≤ ∑ k, ‖(X.Gm.map τ)⁻¹ k l‖ * ‖Y⁻¹ b k‖ := by sorry
