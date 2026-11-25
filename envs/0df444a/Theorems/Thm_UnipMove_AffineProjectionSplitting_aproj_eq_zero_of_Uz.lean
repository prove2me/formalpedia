-- Prove2me | Theorems.Thm_UnipMove_AffineProjectionSplitting_aproj_eq_zero_of_Uz
-- name    : UnipMove.AffineProjectionSplitting.aproj_eq_zero_of_Uz
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:10:59.580508+00:00
-- url     : https://prove2.me/theorems/558e2fd6-f522-4c0e-bb2b-282cf499fa9d
-- title:
--   Affine Projection Splitting: aproj eq zero of Uz
-- statement:
--   The Affine Projection Splitting construction uses the aproj eq zero of Uz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/AprojEqZeroOfUz.lean#L45-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/AprojEqZeroOfUz.lean#L45-L55

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

theorem UnipMove.AffineProjectionSplitting.aproj_eq_zero_of_Uz {x : Frame X.Ψ r} {u : X.Ψ → Fin r → ℂ} (hu : u ∈ X.Uz x ξ) :
    X.aproj x ξ u = 0 := by sorry
