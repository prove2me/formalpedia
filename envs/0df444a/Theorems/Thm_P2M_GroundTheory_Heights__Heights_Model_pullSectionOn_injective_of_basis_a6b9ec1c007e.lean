-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_injective_of_basis_a6b9ec1c007e
-- name    : P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_injective_of_basis_a6b9ec1c007e
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:29:53.667574+00:00
-- url     : https://prove2.me/theorems/07e30a6e-5b03-4e04-b469-0d66596940bf
-- title:
--   P2 M Ground Theory Heights  Heights Model pull Section On injective of basis a6b9ec1c007e: P2 M Ground Theory Heights  Heights Model pull Section On injective of basis a6b9ec1c007e
-- statement:
--   The P2 M Ground Theory Heights  Heights Model pull Section On injective of basis a6b9ec1c007e construction uses the P2 M Ground Theory Heights  Heights Model pull Section On injective of basis a6b9ec1c007e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PClearDenominators.lean#L86-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PClearDenominators.lean#L86-L98

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

theorem P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_injective_of_basis_a6b9ec1c007e :
    Function.Injective (pullSectionOn (baseChangeMap f ℚ) L W) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«pullSectionOn_injective_of_basis» := P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_injective_of_basis_a6b9ec1c007e
