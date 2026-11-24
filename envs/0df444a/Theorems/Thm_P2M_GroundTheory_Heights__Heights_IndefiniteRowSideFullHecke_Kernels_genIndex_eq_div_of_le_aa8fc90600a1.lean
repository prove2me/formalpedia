-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_genIndex_eq_div_of_le_aa8fc90600a1
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_genIndex_eq_div_of_le_aa8fc90600a1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:51.290793+00:00
-- url     : https://prove2.me/theorems/23f6db3a-6a20-4b00-843d-c1bbfc266f15
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels gen Index eq div of le aa8fc90600a1: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels gen Index eq
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels gen Index eq div of le aa8fc90600a1 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels gen Index eq div of le aa8fc90600a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ExistsSmulMemOfSpanEqTop.lean#L13-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ExistsSmulMemOfSpanEqTop.lean#L13-L29

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_genIndex_eq_div_of_le_aa8fc90600a1 {M : Type*} [AddCommGroup M] {A B C : AddSubgroup M} (hCA : C ≤ A)
    (hCB : C ≤ B) (hC : C.relIndex B ≠ 0) :
    genIndex A B = (C.relIndex A : ℝ) / (C.relIndex B : ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«genIndex_eq_div_of_le» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_genIndex_eq_div_of_le_aa8fc90600a1
