-- Prove2me | Theorems.Thm_QEC_Coding_PuncturedReedMuller_wordPairing_restrictKept_eq_of_restrictLow_eq_zero
-- name    : QEC.Coding.PuncturedReedMuller.wordPairing_restrictKept_eq_of_restrictLow_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:03:33.108613+00:00
-- url     : https://prove2.me/theorems/b826e5fc-defd-49c6-8444-32fd8f93db79
-- title:
--   Punctured Reed Muller: word Pairing restrict Kept eq of restrict Low eq zero
-- statement:
--   Removing coordinates on which the left word vanishes preserves its pairing.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L385-L423
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L385-L423

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PuncturedReedMuller
open ReedMuller

theorem QEC.Coding.PuncturedReedMuller.wordPairing_restrictKept_eq_of_restrictLow_eq_zero
    {m w : Nat} (left right : Word (ZMod 2) (BooleanPoint m))
    (hlow : restrictLow m w left = 0) :
    wordPairing (restrictKept m w left) (restrictKept m w right) =
      wordPairing left right := by sorry
