-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoostLowerBounds_plane_facts
-- name    : ReciprocityTheory.ChartRestriction.G.FD.BoostLowerBounds.plane_facts
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:35:17.824886+00:00
-- url     : https://prove2.me/theorems/0145fbad-07f2-42f0-8092-0fb53c6067c3
-- title:
--   Boost Lower Bounds: plane facts
-- statement:
--   The Boost Lower Bounds construction uses the plane facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/BoostLowerBounds.lean#L183-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/BoostLowerBounds.lean#L183-L206

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RankOneBoostIsometries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoostLowerBounds
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
open ReciprocityTheory.ChartRestriction.G.FD.BoostLowerBounds
open MajorantConjugateTransfer FlowMatrixMajorants RankOneBoostIsometries
variable {r : ℕ} (X : Data E r) (τ : X.Ψ) {z : Frame X.Ψ r} (hz : z ∈ X.dom) {e : Fin r → ℂ}
include hz

theorem ReciprocityTheory.ChartRestriction.G.FD.BoostLowerBounds.plane_facts (hee : hermC τ.1 X.Gm e e = 0) (he0 : e ≠ 0) :
    0 < X.maj z τ e ∧ hermC τ.1 X.Gm (X.jp z τ e) (X.jp z τ e) = 0 ∧
      hermC τ.1 X.Gm e (X.jp z τ e) = X.maj z τ e ∧
      hermC τ.1 X.Gm (X.jp z τ e) e = X.maj z τ e := by sorry
