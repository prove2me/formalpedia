-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerInhabit_point_data_824ef48ddc21
-- name    : P2M_GroundTheory_Heights__Heights_MahlerInhabit_point_data_824ef48ddc21
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:48:16.915323+00:00
-- url     : https://prove2.me/theorems/7457ed36-ee56-4b85-a131-29813562c7f7
-- title:
--   P2 M Ground Theory Heights  Heights Mahler Inhabit point data 824ef48ddc21: P2 M Ground Theory Heights  Heights Mahler Inhabit point data 824ef48ddc21
-- statement:
--   The P2 M Ground Theory Heights  Heights Mahler Inhabit point data 824ef48ddc21 construction uses the P2 M Ground Theory Heights  Heights Mahler Inhabit point data 824ef48ddc21 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsMahler.lean#L246-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsMahler.lean#L246-L249

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

theorem P2M_GroundTheory_Heights__Heights_MahlerInhabit_point_data_824ef48ddc21 :
    IsChowCycleData (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1) 0 1 (X (0, 0)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MahlerInhabit».«point_data» := P2M_GroundTheory_Heights__Heights_MahlerInhabit_point_data_824ef48ddc21
