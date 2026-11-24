-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_gramDet_comap_641348eb9df1
-- name    : P2M_GroundTheory_Heights__Heights_gramDet_comap_641348eb9df1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:44.911035+00:00
-- url     : https://prove2.me/theorems/102f594a-32bc-441e-b280-0de66b594196
-- title:
--   P2 M Ground Theory Heights  Heights gram Det comap 641348eb9df1: P2 M Ground Theory Heights  Heights gram Det comap 641348eb9df1
-- statement:
--   The P2 M Ground Theory Heights  Heights gram Det comap 641348eb9df1 construction uses the P2 M Ground Theory Heights  Heights gram Det comap 641348eb9df1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/LinearIndependentSumElimOfExact.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/LinearIndependentSumElimOfExact.lean#L16-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact
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
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open scoped ComplexOrder
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_gramDet_comap_641348eb9df1 {E M : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
    [Module.Projective (𝓞 K) E] [AddCommGroup M] [Module (𝓞 K) M] [Module.Finite (𝓞 K) M]
    [Module.Projective (𝓞 K) M] (h : HermitianMetric K E) (f : M →ₗ[𝓞 K] E)
    (hf : Function.Injective f) (σ : K →+* ℂ) {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → M) :
    gramDet (h.comap f hf) σ s = gramDet h σ (fun i ↦ f (s i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«gramDet_comap» := P2M_GroundTheory_Heights__Heights_gramDet_comap_641348eb9df1
