-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalGraphMass_norm_le_of_frameProj_c4b386709b7d
-- name    : P2M_GroundTheory_Heights__Heights_LocalGraphMass_norm_le_of_frameProj_c4b386709b7d
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:28:35.495786+00:00
-- url     : https://prove2.me/theorems/6011f0cc-5181-43ff-9736-b9332b7a491e
-- title:
--   P2 M Ground Theory Heights  Heights Local Graph Mass norm le of frame Proj c4b386709b7d: P2 M Ground Theory Heights  Heights Local Graph Mass norm le of frame Proj c4b386709b7d
-- statement:
--   The P2 M Ground Theory Heights  Heights Local Graph Mass norm le of frame Proj c4b386709b7d construction uses the P2 M Ground Theory Heights  Heights Local Graph Mass norm le of frame Proj c4b386709b7d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalGraphMass.lean#L17-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalGraphMass.lean#L17-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalGraphMass
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
open MeasureTheory Function
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LocalGraphMass
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_LocalGraphMass_norm_le_of_frameProj_c4b386709b7d (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (z : EuclideanSpace ℂ (Fin n)) (x : EuclideanSpace ℂ I)
    (hx : WithLp.ofLp x = frameProj b I z) : ‖x‖ ≤ ‖z‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LocalGraphMass».«norm_le_of_frameProj» := P2M_GroundTheory_Heights__Heights_LocalGraphMass_norm_le_of_frameProj_c4b386709b7d
