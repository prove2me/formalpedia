-- Prove2me | Theorems.Thm_UnipMove_AffineProjectionSplitting_lineV_mem_Iperp
-- name    : UnipMove.AffineProjectionSplitting.lineV_mem_Iperp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:10:42.01519+00:00
-- url     : https://prove2.me/theorems/f9a17876-09e6-5665-8ca3-83d508665276
-- title:
--   Affine Projection Splitting: line V mem Iperp
-- statement:
--   The Affine Projection Splitting construction uses the line V mem Iperp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/AprojEqZeroOfUz.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/AprojEqZeroOfUz.lean#L29-L32

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

theorem UnipMove.AffineProjectionSplitting.lineV_mem_Iperp (hξ : herm X.Gm ξ ξ = 0) (s : X.Ψ → ℂ) : X.lineV ξ s ∈ X.Iperp ξ := by sorry
