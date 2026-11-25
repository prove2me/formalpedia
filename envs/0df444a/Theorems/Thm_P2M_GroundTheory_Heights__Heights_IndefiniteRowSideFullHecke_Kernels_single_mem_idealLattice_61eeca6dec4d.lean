-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_single_mem_idealLattice_61eeca6dec4d
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_single_mem_idealLattice_61eeca6dec4d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:00:29.408191+00:00
-- url     : https://prove2.me/theorems/9b4165ee-2400-4002-bda4-53514a8c8e1b
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels single mem ideal Lattice 61eeca6dec4d: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels single mem
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels single mem ideal Lattice 61eeca6dec4d construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels single mem ideal Lattice 61eeca6dec4d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/SingleMemIdealLattice.lean#L35-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/SingleMemIdealLattice.lean#L35-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_LatticeBundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_SingleMemIdealLattice
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
open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights TensorProduct
open scoped nonZeroDivisors
noncomputable section
variable {K : Type} [Field K] [NumberField K]
omit [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_single_mem_idealLattice_61eeca6dec4d {n : ℕ} {a : Fin n → FractionalIdeal (𝓞 K)⁰ K} (v : idealLattice a)
    (x : Fin n) : (Pi.single x ((v : Fin n → K) x) : Fin n → K) ∈ idealLattice a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«single_mem_idealLattice» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_single_mem_idealLattice_61eeca6dec4d
