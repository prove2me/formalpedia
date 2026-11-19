-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_mem_l1LogicalCosetWords_iff
-- name    : QEC.Distillation.BK15.mem_l1LogicalCosetWords_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T01:05:55.060867+00:00
-- url     : https://prove2.me/theorems/a81075fc-ee4a-4522-b960-3a1b8c73a7c4
-- title:
--   BK15: mem l1 Logical Coset Words iff
-- statement:
--   The `L1 + [1]` enumeration has its direct coefficient characterization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L612-L626
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L612-L626

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.mem_l1LogicalCosetWords_iff (w : Word) :
    w ∈ l1LogicalCosetWords ↔
      ∃ a : Fin 4 → Bit, w = l1CoefficientMap a + allOnes := by sorry
