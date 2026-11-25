-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_exists_smul_mem_of_span_eq_top_707bad7a4bf7
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_exists_smul_mem_of_span_eq_top_707bad7a4bf7
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:27:00.237869+00:00
-- url     : https://prove2.me/theorems/3c042d86-b73d-47cb-b2dc-befe124d09e2
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels exists smul mem of span eq top 707bad7a4bf7: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels exist
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels exists smul mem of span eq top 707bad7a4bf7 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels exists smul mem of span eq top 707bad7a4bf7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ExistsSmulMemOfSpanEqTop.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ExistsSmulMemOfSpanEqTop.lean#L31-L34

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_exists_smul_mem_of_span_eq_top_707bad7a4bf7 {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (Λ : Submodule (𝓞 K) (Fin n → K)) (hΛ : Submodule.span K (Λ : Set (Fin n → K)) = ⊤)
    (v : Fin n → K) : ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ Λ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«exists_smul_mem_of_span_eq_top» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_exists_smul_mem_of_span_eq_top_707bad7a4bf7
