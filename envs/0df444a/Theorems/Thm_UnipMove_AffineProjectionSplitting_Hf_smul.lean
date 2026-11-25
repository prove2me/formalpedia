-- Prove2me | Theorems.Thm_UnipMove_AffineProjectionSplitting_Hf_smul
-- name    : UnipMove.AffineProjectionSplitting.Hf_smul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:10:59.803097+00:00
-- url     : https://prove2.me/theorems/13f358b5-67c2-492d-beb4-c2ab3df708c5
-- title:
--   Affine Projection Splitting: Hf smul
-- statement:
--   The Affine Projection Splitting construction uses the Hf smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/AprojEqZeroOfUz.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/AprojEqZeroOfUz.lean#L61-L64

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_AprojEqZeroOfUz
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
open UnipMove.AffineProjectionSplitting
variable {r : ℕ} (X : Data E r) (ξ : Fin r → E)

theorem UnipMove.AffineProjectionSplitting.Hf_smul (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (u w : Fin r → ℂ) :
    X.Hf x τ (c • u) w = c * X.Hf x τ u w := by sorry
