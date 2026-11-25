-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_hasFDerivAt_slice_52338e47dd3d
-- name    : P2M_GroundTheory_Heights__Heights_hasFDerivAt_slice_52338e47dd3d
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:46:23.834807+00:00
-- url     : https://prove2.me/theorems/8fd9b8c5-5664-515e-8c2a-8a7df7ff2440
-- title:
--   P2 M Ground Theory Heights  Heights has FDeriv At slice 52338e47dd3d: P2 M Ground Theory Heights  Heights has FDeriv At slice 52338e47dd3d
-- statement:
--   The P2 M Ground Theory Heights  Heights has FDeriv At slice 52338e47dd3d construction uses the P2 M Ground Theory Heights  Heights has FDeriv At slice 52338e47dd3d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceMatricesOpen.lean#L20-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceMatricesOpen.lean#L20-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceMatricesOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGeneralProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceMatricesOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_hasFDerivAt_slice_52338e47dd3d {n k : ℕ} {γ : (Fin (k + 1) → ℂ) → Fin n → ℂ} {s : Fin (k + 1) → ℂ}
    (hγ : DifferentiableAt ℂ γ s) (L : Matrix (Fin k) (Fin n) ℂ) :
    HasFDerivAt (fun t => vecCons (t 0) (L *ᵥ γ t)) (sliceDeriv L (fderiv ℂ γ s)) s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«hasFDerivAt_slice» := P2M_GroundTheory_Heights__Heights_hasFDerivAt_slice_52338e47dd3d
