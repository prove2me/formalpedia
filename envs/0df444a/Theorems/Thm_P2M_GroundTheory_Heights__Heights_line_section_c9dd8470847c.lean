-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_line_section_c9dd8470847c
-- name    : P2M_GroundTheory_Heights__Heights_line_section_c9dd8470847c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:50.001386+00:00
-- url     : https://prove2.me/theorems/1aaeac54-9735-43b7-81e5-d2cf0ed2be70
-- title:
--   P2 M Ground Theory Heights  Heights line section c9dd8470847c: P2 M Ground Theory Heights  Heights line section c9dd8470847c
-- statement:
--   The P2 M Ground Theory Heights  Heights line section c9dd8470847c construction uses the P2 M Ground Theory Heights  Heights line section c9dd8470847c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsSectionOrder.lean#L280-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsSectionOrder.lean#L280-L287

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

theorem P2M_GroundTheory_Heights__Heights_line_section_c9dd8470847c :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) (1 + 1) (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) ∧
      linForm uLine ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧ Prime qLine ∧
      (Ideal.span {qLine}).IsPrime ∧
      ¬ qLine ∣ specFirst (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) tLine := by sorry

alias «GroundTheory».«Heights₂».«Heights».«line_section» := P2M_GroundTheory_Heights__Heights_line_section_c9dd8470847c
