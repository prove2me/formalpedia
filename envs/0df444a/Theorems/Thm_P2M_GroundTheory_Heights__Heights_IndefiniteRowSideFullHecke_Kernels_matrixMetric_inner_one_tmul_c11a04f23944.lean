-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_matrixMetric_inner_one_tmul_c11a04f23944
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_matrixMetric_inner_one_tmul_c11a04f23944
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:26:03.329856+00:00
-- url     : https://prove2.me/theorems/f628046f-cf23-58e0-809c-e5e71959a5e5
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels matrix Metric inner one tmul c11a04f23944: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels matrix
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels matrix Metric inner one tmul c11a04f23944 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels matrix Metric inner one tmul c11a04f23944 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/LatticeBundleObjects.lean#L158-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/LatticeBundleObjects.lean#L158-L165

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardInnerSingleNe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AssemblyLines
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_CommonDenominator
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_LatticeBundleObjects
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
open GroundTheory.Heights₂.Heights.ComplexAt
open scoped nonZeroDivisors ComplexOrder
noncomputable section
variable {K : Type} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_matrixMetric_inner_one_tmul_c11a04f23944 {N : ℕ} (M : Submodule (𝓞 K) (Fin N → K))
    [Module.Finite (𝓞 K) M] (H : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (hH : ∀ σ, (H σ).PosDef)
    (hconj : ∀ σ, H (conjugate σ) = (H σ).map (starRingEnd ℂ)) (σ : K →+* ℂ) (v u : M) :
    ((matrixMetric M H hH hconj).form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] v)
        ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] u) =
      star (embVec σ (v : Fin N → K)) ⬝ᵥ (H σ *ᵥ embVec σ (u : Fin N → K)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«matrixMetric_inner_one_tmul» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_matrixMetric_inner_one_tmul_c11a04f23944
