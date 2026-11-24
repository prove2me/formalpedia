-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianMetric_integers_inner_66e5d940cc4d
-- name    : P2M_GroundTheory_Heights__Heights_HermitianMetric_integers_inner_66e5d940cc4d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:07:52.196266+00:00
-- url     : https://prove2.me/theorems/4e258d21-c794-401f-9f29-db0f1c25b664
-- title:
--   P2 M Ground Theory Heights  Heights Hermitian Metric integers inner 66e5d940cc4d: P2 M Ground Theory Heights  Heights Hermitian Metric integers inner 66e5d940cc4d
-- statement:
--   The P2 M Ground Theory Heights  Heights Hermitian Metric integers inner 66e5d940cc4d construction uses the P2 M Ground Theory Heights  Heights Hermitian Metric integers inner 66e5d940cc4d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HermitianLattice.lean#L154-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HermitianLattice.lean#L154-L157

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct
noncomputable section
open ComplexAt
variable {K : Type*} [Field K]
attribute [instance] HermitianBundle.instAddCommGroup HermitianBundle.instModule
  HermitianBundle.instFinite HermitianBundle.instProjective
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (K)

theorem P2M_GroundTheory_Heights__Heights_HermitianMetric_integers_inner_66e5d940cc4d (σ : K →+* ℂ) (z w : ComplexAt σ) (a b : 𝓞 K) :
    ((HermitianMetric.integers K).form σ).inner (z ⊗ₜ a) (w ⊗ₜ b) =
      starRingEnd ℂ (σ (a : K) * (ofComplex σ).symm z) * (σ (b : K) * (ofComplex σ).symm w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermitianMetric».«integers_inner» := P2M_GroundTheory_Heights__Heights_HermitianMetric_integers_inner_66e5d940cc4d
