-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMeanFubini_measurePreserving_consEquiv_fe40b3b8d4c3
-- name    : P2M_GroundTheory_Heights__Heights_SphereMeanFubini_measurePreserving_consEquiv_fe40b3b8d4c3
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:38:48.386892+00:00
-- url     : https://prove2.me/theorems/61f7681b-6c96-46c2-86bb-b2a1ef68d3f1
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean Fubini measure Preserving cons Equiv fe40b3b8d4c3: P2 M Ground Theory Heights  Heights Sphere Mean Fubini measure Preserving cons Equiv fe40b3b8d4c3
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean Fubini measure Preserving cons Equiv fe40b3b8d4c3 construction uses the P2 M Ground Theory Heights  Heights Sphere Mean Fubini measure Preserving cons Equiv fe40b3b8d4c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSphereMeanFubini.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSphereMeanFubini.lean#L43-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSphereMeanFubini
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
open MeasureTheory Measure Set
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMeanFubini

theorem P2M_GroundTheory_Heights__Heights_SphereMeanFubini_measurePreserving_consEquiv_fe40b3b8d4c3 {n : ℕ} (k : ℕ) :
    MeasurePreserving (consEquiv (n := n) k) volume volume := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMeanFubini».«measurePreserving_consEquiv» := P2M_GroundTheory_Heights__Heights_SphereMeanFubini_measurePreserving_consEquiv_fe40b3b8d4c3
