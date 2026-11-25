-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_norm_pairing_le_f1169a0aed31
-- name    : P2M_GroundTheory_Heights__Heights_HermNorm_norm_pairing_le_f1169a0aed31
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:18:23.432867+00:00
-- url     : https://prove2.me/theorems/4c7ce535-7eb1-41ea-9033-200794b87fa3
-- title:
--   P2 M Ground Theory Heights  Heights Herm Norm norm pairing le f1169a0aed31: P2 M Ground Theory Heights  Heights Herm Norm norm pairing le f1169a0aed31
-- statement:
--   The P2 M Ground Theory Heights  Heights Herm Norm norm pairing le f1169a0aed31 construction uses the P2 M Ground Theory Heights  Heights Herm Norm norm pairing le f1169a0aed31 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLogBound.lean#L14-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLogBound.lean#L14-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
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
open MvPolynomial MeasureTheory NumberField Matrix
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_HermNorm_norm_pairing_le_f1169a0aed31 (h : HermNorm n) (u y : Fin n → ℂ) :
    ‖∑ j, u j * y j‖ ≤ h.norm u * h.dualNorm y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermNorm».«norm_pairing_le» := P2M_GroundTheory_Heights__Heights_HermNorm_norm_pairing_le_f1169a0aed31
