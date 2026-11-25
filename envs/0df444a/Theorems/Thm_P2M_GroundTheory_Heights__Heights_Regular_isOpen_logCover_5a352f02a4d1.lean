-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_isOpen_logCover_5a352f02a4d1
-- name    : P2M_GroundTheory_Heights__Heights_Regular_isOpen_logCover_5a352f02a4d1
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:18:07.049799+00:00
-- url     : https://prove2.me/theorems/1b3c1e38-42ff-5a7e-8136-c5b326c2b610
-- title:
--   P2 M Ground Theory Heights  Heights Regular is Open log Cover 5a352f02a4d1: P2 M Ground Theory Heights  Heights Regular is Open log Cover 5a352f02a4d1
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular is Open log Cover 5a352f02a4d1 construction uses the P2 M Ground Theory Heights  Heights Regular is Open log Cover 5a352f02a4d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PosSemidefOfIntQuadNonneg.lean#L90-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PosSemidefOfIntQuadNonneg.lean#L90-L102

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PosSemidefOfIntQuadNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Topology Filter
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_isOpen_logCover_5a352f02a4d1 {n a : ℕ} (h : a ≤ n) : IsOpen (logCover h) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«isOpen_logCover» := P2M_GroundTheory_Heights__Heights_Regular_isOpen_logCover_5a352f02a4d1
