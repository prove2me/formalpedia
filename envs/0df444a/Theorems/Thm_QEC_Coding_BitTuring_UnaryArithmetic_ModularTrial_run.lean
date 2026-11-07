-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularTrial_run
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial.run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:08:46.048197+00:00
-- url     : https://prove2.me/theorems/dc1062ad-f3e7-48bc-8079-cb2154ff3ca7
-- title:
--   Modular Trial: run
-- statement:
--   The whole genuine machine run cleanly halts at the exact counted step with the correct flag.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryModularTrial.lean#L101-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryModularTrial.lean#L101-L112

import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularProduct
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularTrial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial
open Turing StateTransition
open UnaryOutputEquality

theorem QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial.run (a b r q : ℕ) (hq : 0<q) :
    (fun c => c.bind (TM2.step machine.program))^[steps a b r q]
      (some (machine.init (input a b r q))) =
      some (machine.halt [decide ((a*b)%q=r)]) := by sorry
