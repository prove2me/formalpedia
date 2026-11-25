-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_restrict_map_eq_of_pullback_52248e31ec6e
-- name    : P2M_GroundTheory_Heights__Heights_Model_restrict_map_eq_of_pullback_52248e31ec6e
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:11.915032+00:00
-- url     : https://prove2.me/theorems/a69b4246-1f74-4119-bf24-e6087cd7dbc8
-- title:
--   P2 M Ground Theory Heights  Heights Model restrict map eq of pullback 52248e31ec6e: P2 M Ground Theory Heights  Heights Model restrict map eq of pullback 52248e31ec6e
-- statement:
--   The P2 M Ground Theory Heights  Heights Model restrict map eq of pullback 52248e31ec6e construction uses the P2 M Ground Theory Heights  Heights Model restrict map eq of pullback 52248e31ec6e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PPullbackFaithful.lean#L109-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PPullbackFaithful.lean#L109-L128

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
set_option backward.isDefEq.respectTransparency.types false

theorem P2M_GroundTheory_Heights__Heights_Model_restrict_map_eq_of_pullback_52248e31ec6e {T U : Scheme.{u}} (g : T ⟶ U)
    (hg : ∀ W : U.Opens, Function.Injective (g.app W)) {A B : U.Modules} (V : U.Opens) {n : ℕ}
    {s : Fin n → Γ(B, V)} (hs : IsBasisOn B V s) (ψ₁ ψ₂ : A ⟶ B)
    (h : (Scheme.Modules.pullback g).map ψ₁ = (Scheme.Modules.pullback g).map ψ₂) :
    (Scheme.Modules.restrictFunctor V.ι).map ψ₁ = (Scheme.Modules.restrictFunctor V.ι).map ψ₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«restrict_map_eq_of_pullback» := P2M_GroundTheory_Heights__Heights_Model_restrict_map_eq_of_pullback_52248e31ec6e
