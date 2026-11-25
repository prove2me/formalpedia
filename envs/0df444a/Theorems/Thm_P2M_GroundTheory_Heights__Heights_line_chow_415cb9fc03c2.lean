-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_line_chow_415cb9fc03c2
-- name    : P2M_GroundTheory_Heights__Heights_line_chow_415cb9fc03c2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:48:11.743135+00:00
-- url     : https://prove2.me/theorems/e4a58400-a54e-4275-97e3-76208172ac4e
-- title:
--   P2 M Ground Theory Heights  Heights line chow 415cb9fc03c2: P2 M Ground Theory Heights  Heights line chow 415cb9fc03c2
-- statement:
--   The P2 M Ground Theory Heights  Heights line chow 415cb9fc03c2 construction uses the P2 M Ground Theory Heights  Heights line chow 415cb9fc03c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsSectionOrder.lean#L222-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsSectionOrder.lean#L222-L225

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

theorem P2M_GroundTheory_Heights__Heights_line_chow_415cb9fc03c2 :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) (1 + 1) (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«line_chow» := P2M_GroundTheory_Heights__Heights_line_chow_415cb9fc03c2
