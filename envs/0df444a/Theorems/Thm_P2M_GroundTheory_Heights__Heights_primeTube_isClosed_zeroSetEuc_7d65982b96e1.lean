-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_primeTube_isClosed_zeroSetEuc_7d65982b96e1
-- name    : P2M_GroundTheory_Heights__Heights_primeTube_isClosed_zeroSetEuc_7d65982b96e1
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:50:45.86287+00:00
-- url     : https://prove2.me/theorems/63601034-f587-43e1-bae0-40315f2faf6b
-- title:
--   P2 M Ground Theory Heights  Heights prime Tube is Closed zero Set Euc 7d65982b96e1: P2 M Ground Theory Heights  Heights prime Tube is Closed zero Set Euc 7d65982b96e1
-- statement:
--   The P2 M Ground Theory Heights  Heights prime Tube is Closed zero Set Euc 7d65982b96e1 construction uses the P2 M Ground Theory Heights  Heights prime Tube is Closed zero Set Euc 7d65982b96e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimeTubeVolume.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimeTubeVolume.lean#L18-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeTubeVolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyMassLower
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSmallSetBallCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeTubeVolume
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
open MvPolynomial MeasureTheory ComplexSets Metric
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_primeTube_isClosed_zeroSetEuc_7d65982b96e1 {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) :
    IsClosed (zeroSetEuc J) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«primeTube_isClosed_zeroSetEuc» := P2M_GroundTheory_Heights__Heights_primeTube_isClosed_zeroSetEuc_7d65982b96e1
