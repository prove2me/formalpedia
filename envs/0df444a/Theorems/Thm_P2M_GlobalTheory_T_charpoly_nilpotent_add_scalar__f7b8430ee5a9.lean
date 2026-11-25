-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_charpoly_nilpotent_add_scalar__f7b8430ee5a9
-- name    : P2M_GlobalTheory_T_charpoly_nilpotent_add_scalar__f7b8430ee5a9
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:50.226258+00:00
-- url     : https://prove2.me/theorems/d7382ddc-4ea3-4a5a-9820-427d3698b4a3
-- title:
--   P2 M Global Theory T charpoly nilpotent add scalar  f7b8430ee5a9: P2 M Global Theory T charpoly nilpotent add scalar  f7b8430ee5a9
-- statement:
--   The P2 M Global Theory T charpoly nilpotent add scalar  f7b8430ee5a9 construction uses the P2 M Global Theory T charpoly nilpotent add scalar  f7b8430ee5a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyNilpotentAddScalarStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyNilpotentAddScalarStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyNilpotentAddScalar
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyNilpotentAddScalarStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_charpoly_nilpotent_add_scalar__f7b8430ee5a9 : ∀ (k : Type) [Field k] (n : ℕ) (N : Matrix (Fin n) (Fin n) k) (c : k), IsNilpotent N → (N + Matrix.scalar (Fin n) c).charpoly = (X - C c) ^ n := by sorry

alias «GlobalTheory».«T».«charpoly_nilpotent_add_scalar'» := P2M_GlobalTheory_T_charpoly_nilpotent_add_scalar__f7b8430ee5a9
