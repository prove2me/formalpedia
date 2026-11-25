-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_data_e3a3d31f3424
-- name    : P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_data_e3a3d31f3424
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:48:11.062641+00:00
-- url     : https://prove2.me/theorems/131d3149-1acd-4eb4-a257-bd47186c9aa6
-- title:
--   P2 M Ground Theory Heights  Heights Mahler Inhabit line data e3a3d31f3424: P2 M Ground Theory Heights  Heights Mahler Inhabit line data e3a3d31f3424
-- statement:
--   The P2 M Ground Theory Heights  Heights Mahler Inhabit line data e3a3d31f3424 construction uses the P2 M Ground Theory Heights  Heights Mahler Inhabit line data e3a3d31f3424 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsMahler.lean#L284-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsMahler.lean#L284-L289

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

theorem P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_data_e3a3d31f3424 :
    IsChowCycleData (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) 1 1 LineChowForm.D2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MahlerInhabit».«line_data» := P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_data_e3a3d31f3424
