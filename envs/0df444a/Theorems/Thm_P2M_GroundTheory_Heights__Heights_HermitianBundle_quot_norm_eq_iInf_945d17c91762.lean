-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianBundle_quot_norm_eq_iInf_945d17c91762
-- name    : P2M_GroundTheory_Heights__Heights_HermitianBundle_quot_norm_eq_iInf_945d17c91762
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:35.382803+00:00
-- url     : https://prove2.me/theorems/448cd119-4fc5-4bc9-b06b-6fd4b0ec64fd
-- title:
--   P2 M Ground Theory Heights  Heights Hermitian Bundle quot norm eq i Inf 945d17c91762: P2 M Ground Theory Heights  Heights Hermitian Bundle quot norm eq i Inf 945d17c91762
-- statement:
--   The P2 M Ground Theory Heights  Heights Hermitian Bundle quot norm eq i Inf 945d17c91762 construction uses the P2 M Ground Theory Heights  Heights Hermitian Bundle quot norm eq i Inf 945d17c91762 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/StatementsBundles.lean#L193-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/StatementsBundles.lean#L193-L228

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsBundles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Heights₂.Heights.HermitianBundle
variable (M : HermitianBundle K) (F : Submodule (𝓞 K) M.carrier) (hF : M.Saturated F)

theorem P2M_GroundTheory_Heights__Heights_HermitianBundle_quot_norm_eq_iInf_945d17c91762 (σ : K →+* ℂ) (ξ : Fibre σ (M.carrier ⧸ F)) :
    ‖FibreSpace.equiv (M.quot F hF).metric σ ξ‖ =
      ⨅ x : {x : Fibre σ M.carrier // F.mkQ.lTensor (ComplexAt σ) x = ξ},
        ‖FibreSpace.equiv M.metric σ x.1‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermitianBundle».«quot_norm_eq_iInf» := P2M_GroundTheory_Heights__Heights_HermitianBundle_quot_norm_eq_iInf_945d17c91762
