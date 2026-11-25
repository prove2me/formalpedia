-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_pair_448a64dfacca
-- name    : P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_pair_448a64dfacca
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:47:55.698459+00:00
-- url     : https://prove2.me/theorems/23ab3332-1b2a-574e-852a-7391cf42450f
-- title:
--   P2 M Ground Theory Heights  Heights Mahler Inhabit line pair 448a64dfacca: P2 M Ground Theory Heights  Heights Mahler Inhabit line pair 448a64dfacca
-- statement:
--   The P2 M Ground Theory Heights  Heights Mahler Inhabit line pair 448a64dfacca construction uses the P2 M Ground Theory Heights  Heights Mahler Inhabit line pair 448a64dfacca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsMahler.lean#L319-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsMahler.lean#L319-L333

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

theorem P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_pair_448a64dfacca :
    IsChowCycleData (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) 1 1 LineChowForm.D2 ∧
      IsAdmissible (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) (coord 0) ∧
      IsAdmissible (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) (coord 1) ∧
      IsAdmissible (cycleSection (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) (coord 0)) (coord 1) ∧
      IsAdmissible (cycleSection (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) (coord 1)) (coord 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MahlerInhabit».«line_pair» := P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_pair_448a64dfacca
