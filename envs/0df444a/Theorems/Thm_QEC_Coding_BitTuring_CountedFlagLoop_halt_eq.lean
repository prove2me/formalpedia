-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_CountedFlagLoop_halt_eq
-- name    : QEC.Coding.BitTuring.CountedFlagLoop.halt_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:15:18.256604+00:00
-- url     : https://prove2.me/theorems/a26f6a12-5f40-4a25-ad06-3bcb68307270
-- title:
--   Counted Flag Loop: halt eq
-- statement:
--   The native endpoint is the actual machine clean halt.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/CountedFlagLoop.lean#L65-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/CountedFlagLoop.lean#L65-L65

import Definitions.Def_QEC_Coding_BitTuring_FlagLoop
import Definitions.Def_QEC_Coding_BitTuring_CountedFlagLoop
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.CountedFlagLoop
open Turing StateTransition
variable (A:Machine)

theorem QEC.Coding.BitTuring.CountedFlagLoop.halt_eq (w:List Bool):halt A w=(machine A).halt w:= by sorry
