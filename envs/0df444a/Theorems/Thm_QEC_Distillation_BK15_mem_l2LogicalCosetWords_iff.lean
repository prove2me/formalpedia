-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_mem_l2LogicalCosetWords_iff
-- name    : QEC.Distillation.BK15.mem_l2LogicalCosetWords_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T01:05:52.011823+00:00
-- url     : https://prove2.me/theorems/d68d7676-6a2d-4ea0-9ab3-e677c6e7dcb7
-- title:
--   BK15: mem l2 Logical Coset Words iff
-- statement:
--   The `L2 + [1]` enumeration has its direct coefficient characterization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L595-L609
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L595-L609

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.mem_l2LogicalCosetWords_iff (w : Word) :
    w ∈ l2LogicalCosetWords ↔
      ∃ b : Sum (Fin 4) QuadraticIndex → Bit, w = l2CoefficientMap b + allOnes := by sorry
