-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotientDegreeSplit_hypotheses_inhabited_085e3f664d0f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotientDegreeSplit_hypotheses_inhabited_085e3f664d0f
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:31:33.438716+00:00
-- url     : https://prove2.me/theorems/ea62d460-6e32-4d86-826d-678de085dc75
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 Quotient Degree Split hypotheses inhabited 085e3f664d0f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Heck
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 Quotient Degree Split hypotheses inhabited 085e3f664d0f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 Quotient Degree Split hypotheses inhabited 085e3f664d0f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StdCoordMapInjective.lean#L124-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StdCoordMapInjective.lean#L124-L135

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotientDegreeSplit_hypotheses_inhabited_085e3f664d0f :
    (idealLattice (fun _ : Fin 2 => (1 : FractionalIdeal (𝓞 ℚ)⁰ ℚ))).FG ∧
      Submodule.span ℚ (idealLattice (fun _ : Fin 2 => (1 : FractionalIdeal (𝓞 ℚ)⁰ ℚ)) :
        Set (Fin 2 → ℚ)) = ⊤ ∧
      LinearIndependent ℚ (Sum.elim
        (fun i : Fin 1 => (Pi.single (Fin.castAdd 1 i) 1 : Fin (1 + 1) → ℚ))
        fun j : Fin 1 => (Pi.single (Fin.natAdd 1 j) 1 : Fin (1 + 1) → ℚ)) ∧ 1 + 1 = 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«S6».«QuotientDegreeSplit».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotientDegreeSplit_hypotheses_inhabited_085e3f664d0f
