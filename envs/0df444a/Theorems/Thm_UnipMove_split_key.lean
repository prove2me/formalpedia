-- Prove2me | Theorems.Thm_UnipMove_split_key
-- name    : UnipMove.split_key
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:11:23.048988+00:00
-- url     : https://prove2.me/theorems/7f232863-219c-5dbd-b11b-d2e0e04fd199
-- title:
--   Unip Move: split key
-- statement:
--   The Unip Move construction uses the split key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/AprojEqZeroOfUz.lean#L77-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/AprojEqZeroOfUz.lean#L77-L104

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

theorem UnipMove.split_key {r : ℕ} {X : DataX E r} {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0)
    {z1 z : Frame X.Ψ r} {δ : X.Ψ → (Fin r → ℂ) →ₗ[ℂ] ℂ}
    (hap : ∀ u ∈ X.Iperp ξ, X.aproj z ξ u = X.aproj z1 ξ u - X.lineV ξ (fun τ => δ τ (X.ucomp z1 ξ u τ)))
    (hJ : ∀ u ∈ X.Uz z1 ξ, X.ucomp z ξ (X.Jz z1 u) = X.Jz z (X.ucomp z ξ u))
    {v : X.Ψ → Fin r → ℂ} (hv : v ∈ X.Iperp ξ) (c : ℂ)
    (h1 : X.Jz z1 (X.ucomp z1 ξ v) = c • X.ucomp z1 ξ v) :
    X.Jz z (X.ucomp z ξ v) = c • X.ucomp z ξ v := by sorry
