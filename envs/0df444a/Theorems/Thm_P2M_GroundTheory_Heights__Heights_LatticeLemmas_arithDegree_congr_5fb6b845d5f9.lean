-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_arithDegree_congr_5fb6b845d5f9
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_arithDegree_congr_5fb6b845d5f9
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:38:04.656391+00:00
-- url     : https://prove2.me/theorems/f594fda1-1fec-5c25-8778-444c0d356972
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas arith Degree congr 5fb6b845d5f9: P2 M Ground Theory Heights  Heights Lattice Lemmas arith Degree congr 5fb6b845d5f9
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas arith Degree congr 5fb6b845d5f9 construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas arith Degree congr 5fb6b845d5f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PLocalChange.lean#L21-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PLocalChange.lean#L21-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField IsDedekindDomain TensorProduct ComplexAt
open GroundTheory.Heights₂.Heights
universe u v
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {E E' : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] [AddCommGroup E'] [Module (𝓞 K) E'] [Module.Finite (𝓞 K) E']
  [Module.Projective (𝓞 K) E']

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_arithDegree_congr_5fb6b845d5f9 (h : HermitianMetric K E) (h' : HermitianMetric K E') (e : E' ≃ₗ[𝓞 K] E)
    (he : ∀ (σ : K →+* ℂ) (x y : E'), (h'.form σ).inner ((1 : ComplexAt σ) ⊗ₜ x) (1 ⊗ₜ y) =
      (h.form σ).inner ((1 : ComplexAt σ) ⊗ₜ e x) (1 ⊗ₜ e y)) :
    arithDegree h' = arithDegree h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«arithDegree_congr» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_arithDegree_congr_5fb6b845d5f9
