-- Prove2me | Theorems.Thm_UnipMove_DeltaValuation_posPart_smul
-- name    : UnipMove.DeltaValuation.posPart_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:11:30.585086+00:00
-- url     : https://prove2.me/theorems/5c7ee69a-a9a4-4f2b-9161-2659b285e875
-- title:
--   Delta Valuation: pos Part smul
-- statement:
--   The Delta Valuation construction uses the pos Part smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/HermLinApply.lean#L31-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/HermLinApply.lean#L31-L40

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

theorem UnipMove.DeltaValuation.posPart_smul {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (v : Fin r → ℂ) :
    X.posPart x τ (c • v) = Complex.normSq c * X.posPart x τ v := by sorry
