-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RankOneBoostIsometries_boost_isom
-- name    : ReciprocityTheory.ChartRestriction.G.FD.RankOneBoostIsometries.boost_isom
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:20:33.497824+00:00
-- url     : https://prove2.me/theorems/420c5480-0350-41ce-85a8-a85ddca8e3e4
-- title:
--   Rank One Boost Isometries: boost isom
-- statement:
--   The Rank One Boost Isometries construction uses the boost isom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/RankOneBoostIsometries.lean#L59-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/RankOneBoostIsometries.lean#L59-L70

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatrixMajorants
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RankOneBoostIsometries
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
open ReciprocityTheory.ChartRestriction.G.FD.RankOneBoostIsometries
open MajorantConjugateTransfer FlowMatrixMajorants
variable {r : ℕ} (X : Data E r) (τ : X.Ψ)
variable {e f : Fin r → ℂ} {m : ℝ} (hm : 0 < m) (hee : hermC τ.1 X.Gm e e = 0)
  (hff : hermC τ.1 X.Gm f f = 0) (hef : hermC τ.1 X.Gm e f = m) (hfe : hermC τ.1 X.Gm f e = m)
include hm hee hff hef hfe

theorem ReciprocityTheory.ChartRestriction.G.FD.RankOneBoostIsometries.boost_isom {σ : ℝ} (hσ : 0 < σ) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm (Matrix.mulVec (boost X τ e f m σ) u) (Matrix.mulVec (boost X τ e f m σ) v) =
      hermC τ.1 X.Gm u v := by sorry
