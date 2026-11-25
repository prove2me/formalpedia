-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_withBot_enat_le_pred_3ed6693ab82f
-- name    : P2M_GroundTheory_Heights__Heights_withBot_enat_le_pred_3ed6693ab82f
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:52:46.128047+00:00
-- url     : https://prove2.me/theorems/7488863c-16b5-40e9-8ff5-42d6774517e4
-- title:
--   P2 M Ground Theory Heights  Heights with Bot enat le pred 3ed6693ab82f: P2 M Ground Theory Heights  Heights with Bot enat le pred 3ed6693ab82f
-- statement:
--   The P2 M Ground Theory Heights  Heights with Bot enat le pred 3ed6693ab82f construction uses the P2 M Ground Theory Heights  Heights with Bot enat le pred 3ed6693ab82f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSmallSetTubeVolume.lean#L20-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSmallSetTubeVolume.lean#L20-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSmallSetTubeVolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeTubeVolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSmallSetTubeVolume
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
open MvPolynomial MeasureTheory ComplexSets
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_withBot_enat_le_pred_3ed6693ab82f {x : WithBot ℕ∞} {d : ℕ} (h0 : 0 ≤ x) (h : x < (d : WithBot ℕ∞)) :
    0 < d ∧ x ≤ ((d - 1 : ℕ) : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«withBot_enat_le_pred» := P2M_GroundTheory_Heights__Heights_withBot_enat_le_pred_3ed6693ab82f
