-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_finite_fibre_and_eq_of_specializes_of_isFinite__bb3d4a10e7ef
-- name    : P2M_GlobalTheory_T_finite_fibre_and_eq_of_specializes_of_isFinite__bb3d4a10e7ef
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:06:50.06542+00:00
-- url     : https://prove2.me/theorems/88c37b8c-174a-48b0-a3ac-59c47bfcf2ff
-- title:
--   P2 M Global Theory T finite fibre and eq of specializes of is Finite  bb3d4a10e7ef: P2 M Global Theory T finite fibre and eq of specializes of is Finite  bb3d4a10e7ef
-- statement:
--   The P2 M Global Theory T finite fibre and eq of specializes of is Finite  bb3d4a10e7ef construction uses the P2 M Global Theory T finite fibre and eq of specializes of is Finite  bb3d4a10e7ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteFibreAndEqOfSpecializesOfIsFiniteStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteFibreAndEqOfSpecializesOfIsFiniteStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteFibreAndEqOfSpecializesOfIsFinite
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteFibreAndEqOfSpecializesOfIsFiniteStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_finite_fibre_and_eq_of_specializes_of_isFinite__bb3d4a10e7ef : ∀ (Y Y' : Scheme.{0}) (k : Y' ⟶ Y), IsFinite k → ∀ y : Y, {a : Y' | k a = y}.Finite ∧ ∀ a b : Y', k a = y → k b = y → a ⤳ b → a = b := by sorry

alias «GlobalTheory».«T».«finite_fibre_and_eq_of_specializes_of_isFinite'» := P2M_GlobalTheory_T_finite_fibre_and_eq_of_specializes_of_isFinite__bb3d4a10e7ef
