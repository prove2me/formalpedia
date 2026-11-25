-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_chowCycle_d0f662866bb8
-- name    : P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_chowCycle_d0f662866bb8
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:48:31.751166+00:00
-- url     : https://prove2.me/theorems/9637ca36-3aff-454a-b302-1a5bc09af64a
-- title:
--   P2 M Ground Theory Heights  Heights Mahler Inhabit line chow Cycle d0f662866bb8: P2 M Ground Theory Heights  Heights Mahler Inhabit line chow Cycle d0f662866bb8
-- statement:
--   The P2 M Ground Theory Heights  Heights Mahler Inhabit line chow Cycle d0f662866bb8 construction uses the P2 M Ground Theory Heights  Heights Mahler Inhabit line chow Cycle d0f662866bb8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsMahler.lean#L275-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsMahler.lean#L275-L282

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

theorem P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_chowCycle_d0f662866bb8 :
    IsChowFormCycle (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) 2 LineChowForm.D2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MahlerInhabit».«line_chowCycle» := P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_chowCycle_d0f662866bb8
