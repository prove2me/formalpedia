-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l1Words_disjoint_l1LogicalCosetWords
-- name    : QEC.Distillation.BK15.l1Words_disjoint_l1LogicalCosetWords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T01:04:46.380132+00:00
-- url     : https://prove2.me/theorems/8018986e-bab1-4a7c-9c34-8e438a99ed97
-- title:
--   BK15: l1 Words disjoint l1 Logical Coset Words
-- statement:
--   The nontrivial `L1 + [1]` coset is disjoint from `L1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L524-L538
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L524-L538

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l1Words_disjoint_l1LogicalCosetWords : Disjoint l1Words l1LogicalCosetWords := by sorry
