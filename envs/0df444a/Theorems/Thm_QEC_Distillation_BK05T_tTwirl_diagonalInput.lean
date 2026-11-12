-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_tTwirl_diagonalInput
-- name    : QEC.Distillation.BK05T.tTwirl_diagonalInput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:34:47.977878+00:00
-- url     : https://prove2.me/theorems/6314552c-0c0b-44a9-854f-72c460a61912
-- title:
--   BK05 T: t Twirl diagonal Input
-- statement:
--   The actual CPTP/unitary twirl fixes the BK05 diagonal T0/T1 mixture.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L728-L737
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L728-L737

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Distillation_FiveQubitT_Input
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open OneQubitMagic
open scoped BigOperators

theorem QEC.Distillation.BK05T.tTwirl_diagonalInput
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    tTwirl (tDiagonalInput epsilon hzero hone) = tDiagonalInput epsilon hzero hone := by sorry
