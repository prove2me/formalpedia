-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerInhabit_point_admissible_38b0f2f4122d
-- name    : P2M_GroundTheory_Heights__Heights_MahlerInhabit_point_admissible_38b0f2f4122d
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:27:28.404906+00:00
-- url     : https://prove2.me/theorems/a8b651a2-9eab-4a8e-a8f9-1839b66b9d19
-- title:
--   P2 M Ground Theory Heights  Heights Mahler Inhabit point admissible 38b0f2f4122d: P2 M Ground Theory Heights  Heights Mahler Inhabit point admissible 38b0f2f4122d
-- statement:
--   The P2 M Ground Theory Heights  Heights Mahler Inhabit point admissible 38b0f2f4122d construction uses the P2 M Ground Theory Heights  Heights Mahler Inhabit point admissible 38b0f2f4122d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsMahler.lean#L251-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsMahler.lean#L251-L253

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

theorem P2M_GroundTheory_Heights__Heights_MahlerInhabit_point_admissible_38b0f2f4122d :
    IsAdmissible (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1) (fun _ => 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MahlerInhabit».«point_admissible» := P2M_GroundTheory_Heights__Heights_MahlerInhabit_point_admissible_38b0f2f4122d
