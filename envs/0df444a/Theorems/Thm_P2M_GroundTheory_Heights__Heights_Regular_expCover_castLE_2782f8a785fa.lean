-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_expCover_castLE_2782f8a785fa
-- name    : P2M_GroundTheory_Heights__Heights_Regular_expCover_castLE_2782f8a785fa
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:18:25.97666+00:00
-- url     : https://prove2.me/theorems/bbbfc193-21df-401b-84f0-80d6691ad9bf
-- title:
--   P2 M Ground Theory Heights  Heights Regular exp Cover cast LE 2782f8a785fa: P2 M Ground Theory Heights  Heights Regular exp Cover cast LE 2782f8a785fa
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular exp Cover cast LE 2782f8a785fa construction uses the P2 M Ground Theory Heights  Heights Regular exp Cover cast LE 2782f8a785fa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PosSemidefOfIntQuadNonneg.lean#L136-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PosSemidefOfIntQuadNonneg.lean#L136-L138

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

theorem P2M_GroundTheory_Heights__Heights_Regular_expCover_castLE_2782f8a785fa {n a : ℕ} (h : a ≤ n) (w : Fin n → ℂ) (i : Fin a) :
    expCover a w (Fin.castLE h i) = Complex.exp (w (Fin.castLE h i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«expCover_castLE» := P2M_GroundTheory_Heights__Heights_Regular_expCover_castLE_2782f8a785fa
