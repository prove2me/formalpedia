-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RankOneBoostIsometries_boost_comp
-- name    : ReciprocityTheory.ChartRestriction.G.FD.RankOneBoostIsometries.boost_comp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:23:10.288596+00:00
-- url     : https://prove2.me/theorems/dbaee42b-b5c3-483d-bf6a-c0d4ef7b9a8e
-- title:
--   Rank One Boost Isometries: boost comp
-- statement:
--   The Rank One Boost Isometries construction uses the boost comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/RankOneBoostIsometries.lean#L47-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/RankOneBoostIsometries.lean#L47-L57

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

theorem ReciprocityTheory.ChartRestriction.G.FD.RankOneBoostIsometries.boost_comp {σ : ℝ} (hσ : 0 < σ) (w : Fin r → ℂ) :
    Matrix.mulVec (boost X τ e f m σ) (Matrix.mulVec (boost X τ e f m σ⁻¹) w) = w := by sorry
