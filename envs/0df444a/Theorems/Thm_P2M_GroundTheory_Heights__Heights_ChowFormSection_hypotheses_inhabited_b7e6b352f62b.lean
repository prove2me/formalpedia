-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSection_hypotheses_inhabited_b7e6b352f62b
-- name    : P2M_GroundTheory_Heights__Heights_ChowFormSection_hypotheses_inhabited_b7e6b352f62b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:37.075034+00:00
-- url     : https://prove2.me/theorems/e1529bcd-03d8-46c3-aefc-5c5df113c0f8
-- title:
--   P2 M Ground Theory Heights  Heights Chow Form Section hypotheses inhabited b7e6b352f62b: P2 M Ground Theory Heights  Heights Chow Form Section hypotheses inhabited b7e6b352f62b
-- statement:
--   The P2 M Ground Theory Heights  Heights Chow Form Section hypotheses inhabited b7e6b352f62b construction uses the P2 M Ground Theory Heights  Heights Chow Form Section hypotheses inhabited b7e6b352f62b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/Statements.lean#L377-L381
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/Statements.lean#L377-L381

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

theorem P2M_GroundTheory_Heights__Heights_ChowFormSection_hypotheses_inhabited_b7e6b352f62b :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) (0 + 1) (X (0, 0)) ∧
      linForm (fun _ => (1 : ℚ)) ∉ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowFormSection».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_ChowFormSection_hypotheses_inhabited_b7e6b352f62b
