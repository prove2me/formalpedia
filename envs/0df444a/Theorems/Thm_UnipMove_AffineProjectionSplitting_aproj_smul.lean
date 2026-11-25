-- Prove2me | Theorems.Thm_UnipMove_AffineProjectionSplitting_aproj_smul
-- name    : UnipMove.AffineProjectionSplitting.aproj_smul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:11:10.701873+00:00
-- url     : https://prove2.me/theorems/cdef09d6-f486-4200-8788-bb6fbf9095b4
-- title:
--   Affine Projection Splitting: aproj smul
-- statement:
--   The Affine Projection Splitting construction uses the aproj smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/AprojEqZeroOfUz.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/AprojEqZeroOfUz.lean#L66-L69

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

theorem UnipMove.AffineProjectionSplitting.aproj_smul (x : Frame X.Ψ r) (c : ℂ) (u : X.Ψ → Fin r → ℂ) :
    X.aproj x ξ (c • u) = c • X.aproj x ξ u := by sorry
