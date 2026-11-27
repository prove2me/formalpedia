-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S9_hypotheses_inhabited_1ae21cf550ec
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S9_hypotheses_inhabited_1ae21cf550ec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:23:59.041727+00:00
-- url     : https://prove2.me/theorems/e6510443-ec80-559e-bb7c-0f459a1dfa79
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S9 hypotheses inhabited 1ae21cf550ec: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S9 hypothese
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S9 hypotheses inhabited 1ae21cf550ec construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S9 hypotheses inhabited 1ae21cf550ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ExtendedDataRemainder.lean#L83-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ExtendedDataRemainder.lean#L83-L97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExtendedDataRemainder
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
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S9_hypotheses_inhabited_1ae21cf550ec :
    4 * ((1 : ℕ) : ℝ) * ((1 + 1 : ℕ) : ℝ) ^ 2 ≤ 16 ∧
      IsPsumDecomposition 1 (1 + 1) (restPoly 1 1 1 .last) inhQ ∧
      ∀ (p n' : ℕ) (τ : Fin 1) (k : ℕ), (fun _ _ _ _ => (1 : ℚ)) p n' τ k = 1 ∨
        (fun _ _ _ _ => (1 : ℚ)) p n' τ k = -1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«S9».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S9_hypotheses_inhabited_1ae21cf550ec
