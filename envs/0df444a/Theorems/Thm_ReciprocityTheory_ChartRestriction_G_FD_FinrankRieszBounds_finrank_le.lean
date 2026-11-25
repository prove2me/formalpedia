-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FinrankRieszBounds_finrank_le
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FinrankRieszBounds.finrank_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:29:43.823062+00:00
-- url     : https://prove2.me/theorems/1fea92e3-8a91-46ee-947f-85ecffe7e226
-- title:
--   Finrank Riesz Bounds: finrank le
-- statement:
--   The Finrank Riesz Bounds construction uses the finrank le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FinrankRieszBounds.lean#L85-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FinrankRieszBounds.lean#L85-L154

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscreteLatticeMinimum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FinrankRieszBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.FinrankRieszBounds
open NumberField Complex Module RealTangentSpace
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
variable (z : Frame X.Ψ r) (ξ : Fin r → E) [hz : Fact (z ∈ X.dom)]
omit hz

theorem ReciprocityTheory.ChartRestriction.G.FD.FinrankRieszBounds.finrank_le {ξ : Fin r → E} (hz : z ∈ X.dom) (hξ : X.IsIso ξ) :
    finrank ℝ (VT (X := X) z ξ) ≤ 2 * fdeg E * (r - 2) := by sorry
