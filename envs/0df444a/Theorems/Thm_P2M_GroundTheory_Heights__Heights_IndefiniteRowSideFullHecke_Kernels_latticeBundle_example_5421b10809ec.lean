-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_latticeBundle_example_5421b10809ec
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_latticeBundle_example_5421b10809ec
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:27:43.611072+00:00
-- url     : https://prove2.me/theorems/d6512e6d-323b-49f2-aa1f-340231e7f3ed
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels lattice Bundle example 5421b10809ec: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels lattice Bundl
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels lattice Bundle example 5421b10809ec construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels lattice Bundle example 5421b10809ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/LatticeBundleObjects.lean#L303-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/LatticeBundleObjects.lean#L303-L322

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_latticeBundle_example_5421b10809ec :
    let a : Fin 2 → FractionalIdeal (𝓞 ℚ)⁰ ℚ := fun _ => 1
    let d : (ℚ →+* ℂ) → Fin 2 → ℝ := fun _ _ => 1
    ∃ hd : ∀ σ x, 0 < d σ x, ∃ hc : ∀ σ x, d (conjugate σ) x = d σ x,
    ∃ v : (latticeBundle a d hd hc).carrier,
      ((latticeBundle a d hd hc).metric.form ratEmbedding).inner
        ((1 : ComplexAt ratEmbedding) ⊗ₜ[𝓞 ℚ] v) ((1 : ComplexAt ratEmbedding) ⊗ₜ[𝓞 ℚ] v) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«latticeBundle_example» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_latticeBundle_example_5421b10809ec
