-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerInhabit_point_line_5dbce2abefb8
-- name    : P2M_GroundTheory_Heights__Heights_MahlerInhabit_point_line_5dbce2abefb8
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:48:17.293418+00:00
-- url     : https://prove2.me/theorems/046a3224-0d44-4e9c-8eec-a9f838e411fa
-- title:
--   P2 M Ground Theory Heights  Heights Mahler Inhabit point line 5dbce2abefb8: P2 M Ground Theory Heights  Heights Mahler Inhabit point line 5dbce2abefb8
-- statement:
--   The P2 M Ground Theory Heights  Heights Mahler Inhabit point line 5dbce2abefb8 construction uses the P2 M Ground Theory Heights  Heights Mahler Inhabit point line 5dbce2abefb8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsMahler.lean#L259-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsMahler.lean#L259-L268

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
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
open MvPolynomial MeasureTheory Matrix
noncomputable section
variable {n : ℕ}
open GroundTheory.Heights₂.Heights.MahlerInhabit

theorem P2M_GroundTheory_Heights__Heights_MahlerInhabit_point_line_5dbce2abefb8 :
    ∀ x : Fin 1 → ℂ, (∀ q ∈ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)), eval x q = 0) ↔
      ∃ t : ℂ, x = t • (fun _ => (1 : ℂ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MahlerInhabit».«point_line» := P2M_GroundTheory_Heights__Heights_MahlerInhabit_point_line_5dbce2abefb8
