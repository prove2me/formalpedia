-- Prove2me | Theorems.Thm_UnipMove_AffineProjectionSplitting_ucomp_smul
-- name    : UnipMove.AffineProjectionSplitting.ucomp_smul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:11:00.108652+00:00
-- url     : https://prove2.me/theorems/07edf12f-9d39-405b-bebe-c3152b24330d
-- title:
--   Affine Projection Splitting: ucomp smul
-- statement:
--   The Affine Projection Splitting construction uses the ucomp smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/AprojEqZeroOfUz.lean#L71-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/AprojEqZeroOfUz.lean#L71-L73

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

theorem UnipMove.AffineProjectionSplitting.ucomp_smul (x : Frame X.Ψ r) (c : ℂ) (u : X.Ψ → Fin r → ℂ) :
    X.ucomp x ξ (c • u) = c • X.ucomp x ξ u := by sorry
