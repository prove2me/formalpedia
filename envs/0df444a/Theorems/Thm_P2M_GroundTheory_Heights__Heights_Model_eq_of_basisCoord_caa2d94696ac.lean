-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_eq_of_basisCoord_caa2d94696ac
-- name    : P2M_GroundTheory_Heights__Heights_Model_eq_of_basisCoord_caa2d94696ac
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:29:59.577482+00:00
-- url     : https://prove2.me/theorems/1695ea55-fd83-406b-9db7-37eb5a169380
-- title:
--   P2 M Ground Theory Heights  Heights Model eq of basis Coord caa2d94696ac: P2 M Ground Theory Heights  Heights Model eq of basis Coord caa2d94696ac
-- statement:
--   The P2 M Ground Theory Heights  Heights Model eq of basis Coord caa2d94696ac construction uses the P2 M Ground Theory Heights  Heights Model eq of basis Coord caa2d94696ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PPullbackFaithful.lean#L91-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PPullbackFaithful.lean#L91-L96

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
variable {X : Scheme.{u}} {B : X.Modules} {n : ℕ} {s : Fin n → Γ(B, ⊤)}

theorem P2M_GroundTheory_Heights__Heights_Model_eq_of_basisCoord_caa2d94696ac (hs : IsBasisOn B ⊤ s) {A : X.Modules} (ψ₁ ψ₂ : A ⟶ B)
    (h : ∀ j, ψ₁ ≫ basisCoord hs j = ψ₂ ≫ basisCoord hs j) : ψ₁ = ψ₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«eq_of_basisCoord» := P2M_GroundTheory_Heights__Heights_Model_eq_of_basisCoord_caa2d94696ac
