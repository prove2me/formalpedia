-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_CoordinateDegree_hypotheses_inhabited_94633b985f1c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_CoordinateDegree_hypotheses_inhabited_94633b985f1c
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:31:01.897805+00:00
-- url     : https://prove2.me/theorems/cf96b1b1-7e09-488d-a1fe-e39cc5c37548
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 Coordinate Degree hypotheses inhabited 94633b985f1c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Ke
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 Coordinate Degree hypotheses inhabited 94633b985f1c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 Coordinate Degree hypotheses inhabited 94633b985f1c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StdCoordMapInjective.lean#L107-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StdCoordMapInjective.lean#L107-L122

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardInnerSingleNe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AssemblyLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StdCoordMapInjective
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_hypotheses_inhabited_687dc14d1232

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_CoordinateDegree_hypotheses_inhabited_94633b985f1c :
    Function.Injective (stdCoordMap ℚ 2) ∧
      Submodule.span ℚ (LinearMap.range (stdCoordMap ℚ 2) : Set (Fin 2 → ℚ)) = ⊤ ∧
      (∀ (σ : ℚ →+* ℂ) (v w : Fin 2 → 𝓞 ℚ),
        ((HermitianBundle.standard ℚ 2).metric.form σ).inner
            ((1 : ComplexAt σ) ⊗ₜ[𝓞 ℚ] v) ((1 : ComplexAt σ) ⊗ₜ[𝓞 ℚ] w) =
          star (embVec σ (stdCoordMap ℚ 2 v)) ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ
            embVec σ (stdCoordMap ℚ 2 w))) ∧
      LinearIndependent ℚ (Pi.basisFun ℚ (Fin 2)) ∧
      (⊤ : Submodule (𝓞 ℚ) (Fin 2 → 𝓞 ℚ)).map (stdCoordMap ℚ 2) =
        LinearMap.range (stdCoordMap ℚ 2) ⊓
          (Submodule.span ℚ (Set.range (Pi.basisFun ℚ (Fin 2)))).restrictScalars (𝓞 ℚ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«S6».«CoordinateDegree».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_CoordinateDegree_hypotheses_inhabited_94633b985f1c
