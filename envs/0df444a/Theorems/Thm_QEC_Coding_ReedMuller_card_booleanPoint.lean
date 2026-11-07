-- Prove2me | Theorems.Thm_QEC_Coding_ReedMuller_card_booleanPoint
-- name    : QEC.Coding.ReedMuller.card_booleanPoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:17:20.145873+00:00
-- url     : https://prove2.me/theorems/996f1688-cb20-4e56-875d-3e682ce3b610
-- title:
--   Reed Muller: card boolean Point
-- statement:
--   The Boolean m-cube has exactly 2^m points.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Base.lean#L651-L653
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Base.lean#L651-L653

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_ReedMuller_Base
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.ReedMuller
open scoped BigOperators

theorem QEC.Coding.ReedMuller.card_booleanPoint (m : Nat) :
    Fintype.card (BooleanPoint m) = 2 ^ m := by sorry
