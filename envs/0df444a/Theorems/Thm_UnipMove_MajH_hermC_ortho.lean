-- Prove2me | Theorems.Thm_UnipMove_MajH_hermC_ortho
-- name    : UnipMove.MajH.hermC_ortho
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:11:33.893472+00:00
-- url     : https://prove2.me/theorems/f9b6343d-ba4b-40c1-9049-e8dc082990aa
-- title:
--   Maj H: herm C ortho
-- statement:
--   The Maj H construction uses the herm C ortho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/DotAddRight.lean#L135-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/DotAddRight.lean#L135-L157

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_DotAddRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UnipMove UnipMove.MajH
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds UnipMove.GraphH NumberField Complex
open scoped ComplexConjugate Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem UnipMove.MajH.hermC_ortho {x : Frame X.Ψ r} (ho : X.IsOrtho x) (τ : X.Ψ) (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (mat x τ *ᵥ u) (mat x τ *ᵥ w) =
      dot (top X u) (top X w) - dot (bot X u) (bot X w) := by sorry
