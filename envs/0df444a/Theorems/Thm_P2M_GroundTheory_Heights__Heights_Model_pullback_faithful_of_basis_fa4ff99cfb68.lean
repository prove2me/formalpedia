-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullback_faithful_of_basis_fa4ff99cfb68
-- name    : P2M_GroundTheory_Heights__Heights_Model_pullback_faithful_of_basis_fa4ff99cfb68
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:15.695121+00:00
-- url     : https://prove2.me/theorems/9cf98282-71f6-458f-bc7e-dbea6bb80538
-- title:
--   P2 M Ground Theory Heights  Heights Model pullback faithful of basis fa4ff99cfb68: P2 M Ground Theory Heights  Heights Model pullback faithful of basis fa4ff99cfb68
-- statement:
--   The P2 M Ground Theory Heights  Heights Model pullback faithful of basis fa4ff99cfb68 construction uses the P2 M Ground Theory Heights  Heights Model pullback faithful of basis fa4ff99cfb68 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PPullbackFaithful.lean#L100-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PPullbackFaithful.lean#L100-L105

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsPullbackFaithful
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PPullbackFaithful
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_Model_pullback_faithful_of_basis_fa4ff99cfb68 {T U : Scheme.{u}} (g : T ⟶ U)
    (hg : ∀ W : U.Opens, Function.Injective (g.app W)) {A B : U.Modules} {n : ℕ}
    {s : Fin n → Γ(B, ⊤)} (hs : IsBasisOn B ⊤ s) (ψ₁ ψ₂ : A ⟶ B)
    (h : (Scheme.Modules.pullback g).map ψ₁ = (Scheme.Modules.pullback g).map ψ₂) : ψ₁ = ψ₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«pullback_faithful_of_basis» := P2M_GroundTheory_Heights__Heights_Model_pullback_faithful_of_basis_fa4ff99cfb68
