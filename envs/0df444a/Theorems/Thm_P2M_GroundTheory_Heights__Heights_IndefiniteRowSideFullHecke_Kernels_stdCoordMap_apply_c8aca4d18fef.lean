-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_stdCoordMap_apply_c8aca4d18fef
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_stdCoordMap_apply_c8aca4d18fef
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:50:25.382626+00:00
-- url     : https://prove2.me/theorems/423dd2c8-b99d-4207-8444-e9010cb9f792
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels std Coord Map apply c8aca4d18fef: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels std Coord Map ap
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels std Coord Map apply c8aca4d18fef construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels std Coord Map apply c8aca4d18fef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StdCoordMapInjective.lean#L64-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StdCoordMapInjective.lean#L64-L65

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_stdCoordMap_apply_c8aca4d18fef (K : Type*) [Field K] (n : ℕ) (v : Fin n → 𝓞 K) (i : Fin n) :
    stdCoordMap K n v i = (v i : K) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«stdCoordMap_apply» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_stdCoordMap_apply_c8aca4d18fef
