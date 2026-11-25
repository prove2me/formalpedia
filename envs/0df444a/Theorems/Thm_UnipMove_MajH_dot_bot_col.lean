-- Prove2me | Theorems.Thm_UnipMove_MajH_dot_bot_col
-- name    : UnipMove.MajH.dot_bot_col
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:12:35.110475+00:00
-- url     : https://prove2.me/theorems/85772016-de51-4a5c-882c-a74055435509
-- title:
--   Maj H: dot bot col
-- statement:
--   The Maj H construction uses the dot bot col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/DotAddRight.lean#L179-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/DotAddRight.lean#L179-L182

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

theorem UnipMove.MajH.dot_bot_col (Z : X.Coord) (τ : X.Ψ) (u : Fin r → ℂ) (b : Fin X.p0) :
    dot (bot X u) (bot X (col (X.lowBlock Z τ) (Fin.castLE X.p0_le b))) =
      ((Matrix.of (Z τ))ᴴ *ᵥ bot X u) b := by sorry
