-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l2Words_disjoint_l2LogicalCosetWords
-- name    : QEC.Distillation.BK15.l2Words_disjoint_l2LogicalCosetWords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T01:04:45.693299+00:00
-- url     : https://prove2.me/theorems/e4a85c58-3be6-463b-bf51-f9ad6e672460
-- title:
--   BK15: l2 Words disjoint l2 Logical Coset Words
-- statement:
--   The nontrivial `L2 + [1]` logical coset is disjoint from `L2`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L507-L521
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L507-L521

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l2Words_disjoint_l2LogicalCosetWords : Disjoint l2Words l2LogicalCosetWords := by sorry
