-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_frameProjLin_apply_c62a8e9c3850
-- name    : P2M_GroundTheory_Heights__Heights_frameProjLin_apply_c62a8e9c3850
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:46:15.312089+00:00
-- url     : https://prove2.me/theorems/4989f39d-33ad-468f-9cf2-216ba33dc48f
-- title:
--   P2 M Ground Theory Heights  Heights frame Proj Lin apply c62a8e9c3850: P2 M Ground Theory Heights  Heights frame Proj Lin apply c62a8e9c3850
-- statement:
--   The P2 M Ground Theory Heights  Heights frame Proj Lin apply c62a8e9c3850 construction uses the P2 M Ground Theory Heights  Heights frame Proj Lin apply c62a8e9c3850 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StFrameJacobianSum.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StFrameJacobianSum.lean#L16-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaMultiplicity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFrameJacobianSum
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
open Module
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_frameProjLin_apply_c62a8e9c3850 {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (z : EuclideanSpace ℂ (Fin n)) :
    WithLp.ofLp (frameProjLin b I z) = frameProj b I z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«frameProjLin_apply» := P2M_GroundTheory_Heights__Heights_frameProjLin_apply_c62a8e9c3850
