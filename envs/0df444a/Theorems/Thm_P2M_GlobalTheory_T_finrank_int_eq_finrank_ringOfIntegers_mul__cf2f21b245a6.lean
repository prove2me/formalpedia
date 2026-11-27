-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_finrank_int_eq_finrank_ringOfIntegers_mul__cf2f21b245a6
-- name    : P2M_GlobalTheory_T_finrank_int_eq_finrank_ringOfIntegers_mul__cf2f21b245a6
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:06:57.859533+00:00
-- url     : https://prove2.me/theorems/65e37350-cfd4-412a-8b28-0543e11e8fc7
-- title:
--   P2 M Global Theory T finrank int eq finrank ring Of Integers mul  cf2f21b245a6: P2 M Global Theory T finrank int eq finrank ring Of Integers mul  cf2f21b245a6
-- statement:
--   The P2 M Global Theory T finrank int eq finrank ring Of Integers mul  cf2f21b245a6 construction uses the P2 M Global Theory T finrank int eq finrank ring Of Integers mul  cf2f21b245a6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankIntEqFinrankRingOfIntegersMulStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankIntEqFinrankRingOfIntegersMulStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankIntEqFinrankRingOfIntegersMul
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankIntEqFinrankRingOfIntegersMulStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_finrank_int_eq_finrank_ringOfIntegers_mul__cf2f21b245a6 : ∀ (E : Type) [Field E] [NumberField E] (N : Type) [AddCommGroup N] [Module (𝓞 E) N] [Module.Free ℤ N] [Module.Finite ℤ N], Module.finrank ℤ N = Module.finrank (𝓞 E) N * Module.finrank ℚ E := by sorry

alias «GlobalTheory».«T».«finrank_int_eq_finrank_ringOfIntegers_mul'» := P2M_GlobalTheory_T_finrank_int_eq_finrank_ringOfIntegers_mul__cf2f21b245a6
