-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_stdCoordMap_single_39e32173f68d
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_stdCoordMap_single_39e32173f68d
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:22:53.294275+00:00
-- url     : https://prove2.me/theorems/1d032a3d-ef97-5365-8e34-6d7e9bac10e3
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels std Coord Map single 39e32173f68d: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels std Coord Map s
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels std Coord Map single 39e32173f68d construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels std Coord Map single 39e32173f68d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StdCoordMapInjective.lean#L73-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StdCoordMapInjective.lean#L73-L79

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_stdCoordMap_single_39e32173f68d (K : Type*) [Field K] (n : ℕ) (i : Fin n) :
    stdCoordMap K n (Pi.single i 1) = Pi.single i 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«stdCoordMap_single» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_stdCoordMap_single_39e32173f68d
