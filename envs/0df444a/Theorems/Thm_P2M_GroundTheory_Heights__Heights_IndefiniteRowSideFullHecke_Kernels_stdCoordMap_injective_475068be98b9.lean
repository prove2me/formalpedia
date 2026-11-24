-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_stdCoordMap_injective_475068be98b9
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_stdCoordMap_injective_475068be98b9
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:49.564568+00:00
-- url     : https://prove2.me/theorems/8601befa-2b74-43f7-9fcd-ae27e24ba55f
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels std Coord Map injective 475068be98b9: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels std Coord Ma
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels std Coord Map injective 475068be98b9 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels std Coord Map injective 475068be98b9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StdCoordMapInjective.lean#L67-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StdCoordMapInjective.lean#L67-L71

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_stdCoordMap_injective_475068be98b9 (K : Type*) [Field K] (n : ℕ) :
    Function.Injective (stdCoordMap K n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«stdCoordMap_injective» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_stdCoordMap_injective_475068be98b9
