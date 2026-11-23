-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RankOneBoostIsometries_boost_mulVec
-- name    : ReciprocityTheory.ChartRestriction.G.FD.RankOneBoostIsometries.boost_mulVec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:32:42.478958+00:00
-- url     : https://prove2.me/theorems/0572a8ae-eb28-4673-b200-b8208e4adfa5
-- title:
--   Rank One Boost Isometries: boost mul Vec
-- statement:
--   The Rank One Boost Isometries construction uses the boost mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/RankOneBoostIsometries.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/RankOneBoostIsometries.lean#L33-L38

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

theorem ReciprocityTheory.ChartRestriction.G.FD.RankOneBoostIsometries.boost_mulVec (e f : Fin r → ℂ) (m σ : ℝ) (v : Fin r → ℂ) :
    Matrix.mulVec (boost X τ e f m σ) v =
      v + ((((σ - 1) / m : ℝ) : ℂ) * hermC τ.1 X.Gm v f) • e +
        ((((σ⁻¹ - 1) / m : ℝ) : ℂ) * hermC τ.1 X.Gm v e) • f := by sorry
