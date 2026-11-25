-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_standard_inner_single_ne_650d14c0e8b4
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_standard_inner_single_ne_650d14c0e8b4
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:21:09.259352+00:00
-- url     : https://prove2.me/theorems/4129f54e-ef50-4739-bdb0-7cca9480ed57
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels standard inner single ne 650d14c0e8b4: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels standard in
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels standard inner single ne 650d14c0e8b4 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels standard inner single ne 650d14c0e8b4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardInnerSingleNe.lean#L45-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardInnerSingleNe.lean#L45-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardInnerSingleNe
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
open NumberField TensorProduct GroundTheory.Heights₂.Heights
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_standard_inner_single_ne_650d14c0e8b4 (K : Type*) [Field K] [NumberField K] (σ : K →+* ℂ)
    (x y : Fin 2) (hxy : x ≠ y) (a b : 𝓞 K) :
    ((HermitianMetric.standard K (Fin 2)).form σ).inner
      ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] (Pi.single x a : Fin 2 → 𝓞 K))
      ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] (Pi.single y b : Fin 2 → 𝓞 K)) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«standard_inner_single_ne» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_standard_inner_single_ne_650d14c0e8b4
