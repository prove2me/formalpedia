-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RankOneBoostIsometries_rk_mulVec
-- name    : ReciprocityTheory.ChartRestriction.G.FD.RankOneBoostIsometries.rk_mulVec
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:20:37.263301+00:00
-- url     : https://prove2.me/theorems/2f53fa39-34bd-4a9a-87da-ef0a00aeff79
-- title:
--   Rank One Boost Isometries: rk mul Vec
-- statement:
--   The Rank One Boost Isometries construction uses the rk mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/RankOneBoostIsometries.lean#L19-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/RankOneBoostIsometries.lean#L19-L28

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

theorem ReciprocityTheory.ChartRestriction.G.FD.RankOneBoostIsometries.rk_mulVec (p w v : Fin r → ℂ) :
    Matrix.mulVec (rk X τ p w) v = hermC τ.1 X.Gm v w • p := by sorry
