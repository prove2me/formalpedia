-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_LatticeAsBundle_hypotheses_inhabited_2b13e1235568
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_LatticeAsBundle_hypotheses_inhabited_2b13e1235568
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:33:49.698693+00:00
-- url     : https://prove2.me/theorems/a5554ceb-6a21-414d-aac5-2ceae41a8f11
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 Lattice As Bundle hypotheses inhabited 2b13e1235568: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Ke
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 Lattice As Bundle hypotheses inhabited 2b13e1235568 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 Lattice As Bundle hypotheses inhabited 2b13e1235568 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ImportsRest.lean#L30-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ImportsRest.lean#L30-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardInnerSingleNe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsRest
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
open NumberField NumberField.ComplexEmbedding GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_LatticeAsBundle_hypotheses_inhabited_2b13e1235568 :
    let a : Fin 2 → FractionalIdeal (𝓞 ℚ)⁰ ℚ := fun _ => 1
    let d : (ℚ →+* ℂ) → Fin 2 → ℝ := fun _ _ => 1
    let b : Fin 1 → Fin 2 → ℚ := fun _ => Pi.single 0 1
    let c : Fin 1 → Fin 2 → ℚ := fun _ => Pi.single 1 1
    (∀ x, a x ≠ 0) ∧ (∀ σ x, 0 < d σ x) ∧ (∀ σ x, d (conjugate σ) x = d σ x) ∧
      LinearIndependent ℚ (Sum.elim b c) ∧ 1 + 1 = 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«S6».«LatticeAsBundle».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_LatticeAsBundle_hypotheses_inhabited_2b13e1235568
