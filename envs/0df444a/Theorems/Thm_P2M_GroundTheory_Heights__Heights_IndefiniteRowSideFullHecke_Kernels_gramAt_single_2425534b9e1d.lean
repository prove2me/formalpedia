-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_gramAt_single_2425534b9e1d
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_gramAt_single_2425534b9e1d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:44:01.30145+00:00
-- url     : https://prove2.me/theorems/060bec3c-f609-488d-8e67-b0277c194a72
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels gram At single 2425534b9e1d: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels gram At single 242553
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels gram At single 2425534b9e1d construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels gram At single 2425534b9e1d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ReMulOfPos.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ReMulOfPos.lean#L12-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ReMulOfPos
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
open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors ComplexOrder
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_gramAt_single_2425534b9e1d {K : Type*} [Field K] {k : ℕ} (h : Matrix (Fin k) (Fin k) ℂ) (σ : K →+* ℂ) :
    gramAt h σ (fun j : Fin k => (Pi.single j 1 : Fin k → K)) = h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«gramAt_single» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_gramAt_single_2425534b9e1d
