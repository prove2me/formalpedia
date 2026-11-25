-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerInhabit_point_relevant_8a932349755c
-- name    : P2M_GroundTheory_Heights__Heights_MahlerInhabit_point_relevant_8a932349755c
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:48:53.059115+00:00
-- url     : https://prove2.me/theorems/ecd8cd8b-4003-42ca-8421-291b91268578
-- title:
--   P2 M Ground Theory Heights  Heights Mahler Inhabit point relevant 8a932349755c: P2 M Ground Theory Heights  Heights Mahler Inhabit point relevant 8a932349755c
-- statement:
--   The P2 M Ground Theory Heights  Heights Mahler Inhabit point relevant 8a932349755c construction uses the P2 M Ground Theory Heights  Heights Mahler Inhabit point relevant 8a932349755c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsMahler.lean#L255-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsMahler.lean#L255-L257

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

theorem P2M_GroundTheory_Heights__Heights_MahlerInhabit_point_relevant_8a932349755c :
    ∀ W ∈ (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1).support, IsRelevant W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MahlerInhabit».«point_relevant» := P2M_GroundTheory_Heights__Heights_MahlerInhabit_point_relevant_8a932349755c
