-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_line_component_84026460324b
-- name    : P2M_GroundTheory_Heights__Heights_line_component_84026460324b
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:51.906258+00:00
-- url     : https://prove2.me/theorems/aafe7b1f-d625-4552-a899-6c0379a1e5b1
-- title:
--   P2 M Ground Theory Heights  Heights line component 84026460324b: P2 M Ground Theory Heights  Heights line component 84026460324b
-- statement:
--   The P2 M Ground Theory Heights  Heights line component 84026460324b construction uses the P2 M Ground Theory Heights  Heights line component 84026460324b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsSectionOrder.lean#L305-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsSectionOrder.lean#L305-L310

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
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
open MvPolynomial
noncomputable section
open LineChowForm

theorem P2M_GroundTheory_Heights__Heights_line_component_84026460324b :
    Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)} ∈
        relComps ((⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ⊔ Ideal.span {linForm uLine}) ∧
      qLine ∈ incIdeal (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) 1 ∧
      linForm tLine ∉ Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«line_component» := P2M_GroundTheory_Heights__Heights_line_component_84026460324b
