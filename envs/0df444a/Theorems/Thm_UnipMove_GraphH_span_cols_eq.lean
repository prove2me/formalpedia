-- Prove2me | Theorems.Thm_UnipMove_GraphH_span_cols_eq
-- name    : UnipMove.GraphH.span_cols_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:12:12.66001+00:00
-- url     : https://prove2.me/theorems/f56f0cfb-35ec-411e-bcf6-31580568f5f9
-- title:
--   Graph H: span cols eq
-- statement:
--   The Graph H construction uses the span cols eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/BotMulVecExt.lean#L200-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/BotMulVecExt.lean#L200-L222

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UnipMove UnipMove.GraphH
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds NumberField Complex
open scoped ComplexConjugate Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem UnipMove.GraphH.span_cols_eq {p : ℕ} (u w : Fin p → Fin r → ℂ) (A : Matrix (Fin p) (Fin p) ℂ)
    (hA : IsUnit A.det) (h : ∀ a, u a = ∑ b, A b a • w b) :
    Submodule.span ℂ (Set.range u) = Submodule.span ℂ (Set.range w) := by sorry
