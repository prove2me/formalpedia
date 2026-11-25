-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_bijective_iff_det_ne_zero_9bac468e1b7a
-- name    : P2M_GroundTheory_Heights__Heights_bijective_iff_det_ne_zero_9bac468e1b7a
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:44:47.241095+00:00
-- url     : https://prove2.me/theorems/d77ddeb5-035f-48bd-aec7-02bdfb1c68ea
-- title:
--   P2 M Ground Theory Heights  Heights bijective iff det ne zero 9bac468e1b7a: P2 M Ground Theory Heights  Heights bijective iff det ne zero 9bac468e1b7a
-- statement:
--   The P2 M Ground Theory Heights  Heights bijective iff det ne zero 9bac468e1b7a construction uses the P2 M Ground Theory Heights  Heights bijective iff det ne zero 9bac468e1b7a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceMatricesOpen.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceMatricesOpen.lean#L30-L34

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

theorem P2M_GroundTheory_Heights__Heights_bijective_iff_det_ne_zero_9bac468e1b7a {N : ℕ} (f : (Fin N → ℂ) →L[ℂ] (Fin N → ℂ)) :
    Function.Bijective f ↔ LinearMap.det (f : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ)) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«bijective_iff_det_ne_zero» := P2M_GroundTheory_Heights__Heights_bijective_iff_det_ne_zero_9bac468e1b7a
