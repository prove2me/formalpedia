-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_chowDegree_point_19e6c3cee704
-- name    : P2M_GroundTheory_Heights__Heights_chowDegree_point_19e6c3cee704
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:40:49.462845+00:00
-- url     : https://prove2.me/theorems/1116609e-52d8-4b7c-af98-af9365247b24
-- title:
--   P2 M Ground Theory Heights  Heights chow Degree point 19e6c3cee704: P2 M Ground Theory Heights  Heights chow Degree point 19e6c3cee704
-- statement:
--   The P2 M Ground Theory Heights  Heights chow Degree point 19e6c3cee704 construction uses the P2 M Ground Theory Heights  Heights chow Degree point 19e6c3cee704 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/Statements.lean#L349-L372
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/Statements.lean#L349-L372

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
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
open MvPolynomial MeasureTheory NumberField
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_chowDegree_point_19e6c3cee704 (F : Type*) [Field F] :
    chowDegree (⊥ : Ideal (MvPolynomial (Fin 1) F)) 1 = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«chowDegree_point» := P2M_GroundTheory_Heights__Heights_chowDegree_point_19e6c3cee704
