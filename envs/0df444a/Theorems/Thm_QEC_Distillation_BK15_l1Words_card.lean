-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l1Words_card
-- name    : QEC.Distillation.BK15.l1Words_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:56:12.826276+00:00
-- url     : https://prove2.me/theorems/aab69987-e931-4dc2-949c-e00460467bf7
-- title:
--   BK15: l1 Words card
-- statement:
--   The direct finite enumerations have their expected cardinalities.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L541-L543
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L541-L543

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l1Words_card : l1Words.card = 16 := by sorry
