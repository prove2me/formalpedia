-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_sliceDeriv_apply_5c592b69efa7
-- name    : P2M_GroundTheory_Heights__Heights_sliceDeriv_apply_5c592b69efa7
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:50:31.497604+00:00
-- url     : https://prove2.me/theorems/eabc0216-5196-4e53-be0b-5f997e08b3c2
-- title:
--   P2 M Ground Theory Heights  Heights slice Deriv apply 5c592b69efa7: P2 M Ground Theory Heights  Heights slice Deriv apply 5c592b69efa7
-- statement:
--   The P2 M Ground Theory Heights  Heights slice Deriv apply 5c592b69efa7 construction uses the P2 M Ground Theory Heights  Heights slice Deriv apply 5c592b69efa7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceMatricesOpen.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceMatricesOpen.lean#L17-L18

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

theorem P2M_GroundTheory_Heights__Heights_sliceDeriv_apply_5c592b69efa7 {n k : ℕ} (L : Matrix (Fin k) (Fin n) ℂ) (D : (Fin (k + 1) → ℂ) →L[ℂ] (Fin n → ℂ))
    (v : Fin (k + 1) → ℂ) : sliceDeriv L D v = vecCons (v 0) (L *ᵥ D v) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«sliceDeriv_apply» := P2M_GroundTheory_Heights__Heights_sliceDeriv_apply_5c592b69efa7
