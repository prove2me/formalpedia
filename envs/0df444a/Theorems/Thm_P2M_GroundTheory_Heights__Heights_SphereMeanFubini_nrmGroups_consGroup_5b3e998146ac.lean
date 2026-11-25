-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMeanFubini_nrmGroups_consGroup_5b3e998146ac
-- name    : P2M_GroundTheory_Heights__Heights_SphereMeanFubini_nrmGroups_consGroup_5b3e998146ac
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:38:47.611991+00:00
-- url     : https://prove2.me/theorems/20dc345d-8111-41e3-9018-5708e79a397e
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean Fubini nrm Groups cons Group 5b3e998146ac: P2 M Ground Theory Heights  Heights Sphere Mean Fubini nrm Groups cons Group 5b3e998146ac
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean Fubini nrm Groups cons Group 5b3e998146ac construction uses the P2 M Ground Theory Heights  Heights Sphere Mean Fubini nrm Groups cons Group 5b3e998146ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSphereMeanFubini.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSphereMeanFubini.lean#L55-L58

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

theorem P2M_GroundTheory_Heights__Heights_SphereMeanFubini_nrmGroups_consGroup_5b3e998146ac {n : ℕ} (h : HermNorm n) (k : ℕ) (v : Fin n → ℂ) (w : Fin k × Fin n → ℂ) :
    nrmGroups h (k + 1) (consGroup v w) = consGroup (nrmv h v) (nrmGroups h k w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMeanFubini».«nrmGroups_consGroup» := P2M_GroundTheory_Heights__Heights_SphereMeanFubini_nrmGroups_consGroup_5b3e998146ac
