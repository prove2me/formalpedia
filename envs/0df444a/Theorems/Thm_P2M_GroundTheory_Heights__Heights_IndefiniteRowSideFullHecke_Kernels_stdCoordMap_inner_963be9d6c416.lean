-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_stdCoordMap_inner_963be9d6c416
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_stdCoordMap_inner_963be9d6c416
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:21:44.164876+00:00
-- url     : https://prove2.me/theorems/0d745ef6-32a4-56b5-a11c-5b02a1a72115
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels std Coord Map inner 963be9d6c416: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels std Coord Map in
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels std Coord Map inner 963be9d6c416 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels std Coord Map inner 963be9d6c416 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StdCoordMapInjective.lean#L88-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StdCoordMapInjective.lean#L88-L99

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardInnerSingleNe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AssemblyLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StdCoordMapInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField NumberField.ComplexEmbedding TensorProduct Matrix GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_stdCoordMap_inner_963be9d6c416 (K : Type*) [Field K] [NumberField K] (n : ℕ) (σ : K →+* ℂ)
    (v w : Fin n → 𝓞 K) :
    ((HermitianBundle.standard K n).metric.form σ).inner
        ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] v) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] w) =
      star (embVec σ (stdCoordMap K n v)) ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) ℂ) *ᵥ
        embVec σ (stdCoordMap K n w)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«stdCoordMap_inner» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_stdCoordMap_inner_963be9d6c416
