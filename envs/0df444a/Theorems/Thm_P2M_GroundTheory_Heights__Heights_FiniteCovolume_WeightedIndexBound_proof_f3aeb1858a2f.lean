-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_WeightedIndexBound_proof_f3aeb1858a2f
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_WeightedIndexBound_proof_f3aeb1858a2f
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:42:37.301028+00:00
-- url     : https://prove2.me/theorems/45bdfdd2-647d-5faf-ad23-310dbc22dd3c
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Weighted Index Bound proof f3aeb1858a2f: P2 M Ground Theory Heights  Heights Finite Covolume Weighted Index Bound proof f3aeb1858a2f
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Weighted Index Bound proof f3aeb1858a2f construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Weighted Index Bound proof f3aeb1858a2f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PWeightedIndexBound.lean#L8-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PWeightedIndexBound.lean#L8-L95

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PWeightedIndexBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField Module

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_WeightedIndexBound_proof_f3aeb1858a2f (E : Type*) [Field E] [NumberField E] [IsTotallyComplex E]
    (h₁ : CoeffLatticeBasis.Statement E) (h₂ : IndexLeDet.Statement E)
    (h₃ : WeightedNormSq.Statement E) (h₄ : WeightedSpaceDim.Statement E)
    (h₅ : ∀ [Fact (finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E)],
      MinkowskiVolumeForm.Statement (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) (finrank ℚ E))
    (h₆ : ∀ [Fact (finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E)],
      VolumeFormIntComb.Statement (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) (finrank ℚ E)) :
    WeightedIndexBound.Statement E := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«WeightedIndexBound».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_WeightedIndexBound_proof_f3aeb1858a2f
