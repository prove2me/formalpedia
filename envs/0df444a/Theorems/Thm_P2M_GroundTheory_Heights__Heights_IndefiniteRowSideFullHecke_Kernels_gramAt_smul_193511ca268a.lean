-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_gramAt_smul_193511ca268a
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_gramAt_smul_193511ca268a
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:35:56.770557+00:00
-- url     : https://prove2.me/theorems/fb26eb82-7b5e-545c-88d9-d08257f55adb
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels gram At smul 193511ca268a: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels gram At smul 193511ca26
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels gram At smul 193511ca268a construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels gram At smul 193511ca268a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ExistsSmulMemOfSpanEqTop.lean#L36-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ExistsSmulMemOfSpanEqTop.lean#L36-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StdCoordMapInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_SpanEqTopSmul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulMemOfSpanEqTop
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
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_gramAt_smul_193511ca268a {K : Type*} [Field K] {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ)
    {ι : Type*} (u : ι → Fin n → K) (c : K) :
    gramAt h σ (fun a => c • u a) = ((‖σ c‖ ^ 2 : ℝ) : ℂ) • gramAt h σ u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«gramAt_smul» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_gramAt_smul_193511ca268a
