-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_measurePreserving_circle_smul_8915803838c3
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_measurePreserving_circle_smul_8915803838c3
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:35.810659+00:00
-- url     : https://prove2.me/theorems/c2c6ffe7-9dcd-49d2-97e2-13c3bc45a93c
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel measure Preserving circle smul 8915803838c3: P2 M Ground Theory Heights  Heights Hilbert Samuel measure Preserving circle smul 8915803838c3
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel measure Preserving circle smul 8915803838c3 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel measure Preserving circle smul 8915803838c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PolydiscMean.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PolydiscMean.lean#L11-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PolydiscMean
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Set Metric Real
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_measurePreserving_circle_smul_8915803838c3 {D : ℕ} (u : Circle) :
    MeasurePreserving (fun z : Fin D → ℂ => (u : ℂ) • z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«measurePreserving_circle_smul» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_measurePreserving_circle_smul_8915803838c3
