-- Prove2me | Theorems.Thm_UnipMove_DeltaValuation_hermLin_apply
-- name    : UnipMove.DeltaValuation.hermLin_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:11:22.304672+00:00
-- url     : https://prove2.me/theorems/db8d1496-c111-519b-bcae-516066024b82
-- title:
--   Delta Valuation: herm Lin apply
-- statement:
--   The Delta Valuation construction uses the herm Lin apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/HermLinApply.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/HermLinApply.lean#L28-L29

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_HermLinApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UnipMove
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open UnipMove.DeltaValuation

theorem UnipMove.DeltaValuation.hermLin_apply {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (K : ℂ) (w v : Fin r → ℂ) :
    hermLin τ G K w v = K * hermC τ G v w := by sorry
