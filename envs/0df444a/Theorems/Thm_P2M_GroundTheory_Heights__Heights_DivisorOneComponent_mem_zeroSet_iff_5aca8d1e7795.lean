-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DivisorOneComponent_mem_zeroSet_iff_5aca8d1e7795
-- name    : P2M_GroundTheory_Heights__Heights_DivisorOneComponent_mem_zeroSet_iff_5aca8d1e7795
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:18:09.011905+00:00
-- url     : https://prove2.me/theorems/3b0019c7-abed-49f5-ae3d-ccad64d7e238
-- title:
--   P2 M Ground Theory Heights  Heights Divisor One Component mem zero Set iff 5aca8d1e7795: P2 M Ground Theory Heights  Heights Divisor One Component mem zero Set iff 5aca8d1e7795
-- statement:
--   The P2 M Ground Theory Heights  Heights Divisor One Component mem zero Set iff 5aca8d1e7795 construction uses the P2 M Ground Theory Heights  Heights Divisor One Component mem zero Set iff 5aca8d1e7795 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PDivisorOneComponent.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PDivisorOneComponent.lean#L15-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorOneComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceMultGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDivisorOneComponent
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
open MvPolynomial Filter Topology ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.DivisorOneComponent

theorem P2M_GroundTheory_Heights__Heights_DivisorOneComponent_mem_zeroSet_iff_5aca8d1e7795 {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    q ∈ zeroSet K ↔ K ≤ RingHom.ker (eval q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DivisorOneComponent».«mem_zeroSet_iff» := P2M_GroundTheory_Heights__Heights_DivisorOneComponent_mem_zeroSet_iff_5aca8d1e7795
