-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_hypotheses_seven_bc998a3eb803
-- name    : P2M_GroundTheory_Heights__Theta_hypotheses_seven_bc998a3eb803
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:42:08.732434+00:00
-- url     : https://prove2.me/theorems/5bb29211-5cd2-5d26-a42e-04e384f499f5
-- title:
--   P2 M Ground Theory Heights  Theta hypotheses seven bc998a3eb803: P2 M Ground Theory Heights  Theta hypotheses seven bc998a3eb803
-- statement:
--   The P2 M Ground Theory Heights  Theta hypotheses seven bc998a3eb803 construction uses the P2 M Ground Theory Heights  Theta hypotheses seven bc998a3eb803 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/QuadraticFieldSqrtNegSeven.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/QuadraticFieldSqrtNegSeven.lean#L44-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_QuadraticFieldSqrtNegSeven
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open NumberField

theorem P2M_GroundTheory_Heights__Theta_hypotheses_seven_bc998a3eb803 :
    Nat.Prime 7 ∧ 7 % 16 = 7 ∧ Module.finrank ℚ QuadraticFieldSqrtNegSeven = 2 ∧
      (∃ x : QuadraticFieldSqrtNegSeven, x ^ 2 = -((7 : ℕ) : QuadraticFieldSqrtNegSeven)) ∧ Nonempty (QuadraticFieldSqrtNegSeven →+* ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«hypotheses_seven» := P2M_GroundTheory_Heights__Theta_hypotheses_seven_bc998a3eb803
