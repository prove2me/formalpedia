-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_pullSectionOn_eq_nsmul_of_basis_f891758361c0
-- name    : P2M_GroundTheory_Heights__Heights_Model_exists_pullSectionOn_eq_nsmul_of_basis_f891758361c0
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:30:47.019785+00:00
-- url     : https://prove2.me/theorems/37120a40-c12e-434f-aa9d-e6d3bc33c77e
-- title:
--   P2 M Ground Theory Heights  Heights Model exists pull Section On eq nsmul of basis f891758361c0: P2 M Ground Theory Heights  Heights Model exists pull Section On eq nsmul of basis f891758361c0
-- statement:
--   The P2 M Ground Theory Heights  Heights Model exists pull Section On eq nsmul of basis f891758361c0 construction uses the P2 M Ground Theory Heights  Heights Model exists pull Section On eq nsmul of basis f891758361c0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PClearDenominators.lean#L100-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PClearDenominators.lean#L100-L110

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PullbackBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_RatLocalAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
variable (hPB : PullbackBasis.Statement.{0}) (hRL : RatLocalAffine.Statement)
  {X : Scheme.{0}} (f : X ⟶ SpecZ) [Flat f] (L : X.Modules)
  {W : X.Opens} (hW : IsAffineOpen W) {n : ℕ} {t : Fin n → Γ(L, W)} (ht : IsBasisOn L W t)
include hPB hRL hW ht

theorem P2M_GroundTheory_Heights__Heights_Model_exists_pullSectionOn_eq_nsmul_of_basis_f891758361c0
    (σ : Γ((Scheme.Modules.pullback (baseChangeMap f ℚ)).obj L, baseChangeMap f ℚ ⁻¹ᵁ W)) :
    ∃ N : ℕ, 0 < N ∧ ∃ τ : Γ(L, W), pullSectionOn (baseChangeMap f ℚ) L W τ = N • σ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«exists_pullSectionOn_eq_nsmul_of_basis» := P2M_GroundTheory_Heights__Heights_Model_exists_pullSectionOn_eq_nsmul_of_basis_f891758361c0
