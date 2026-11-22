-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15AcceptedLayer_dephased_eq_nextResource
-- name    : QEC.Distillation.BK15.Threshold.bk15AcceptedLayer_dephased_eq_nextResource
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:28:00.736683+00:00
-- url     : https://prove2.me/theorems/31f894d7-8738-42e0-9677-21aa1af82409
-- title:
--   Threshold: bk15 Accepted Layer dephased eq next Resource
-- statement:
--   Dephasing the actual accepted output produces exactly the diagonal
--   resource required at the next scheduled depth.  This is the physical handoff
--   between consecutive selected accepted layers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L668-L682
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L668-L682

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Threshold
open Semantics Semantics.Qubit
open NoisyInput Protocol Recurrence
open OneQubitMagic

theorem QEC.Distillation.BK15.Threshold.bk15AcceptedLayer_dephased_eq_nextResource
    (epsilon : Real) (hpositive : 0 < epsilon)
    (hthreshold : epsilon < epsilonStar) (rounds : Nat) :
    aBasisDephasing.mapDensity
        (bk15AcceptedLayer epsilon hpositive hthreshold rounds) =
      diagonalAResource
        (bk15IterationEpsilon epsilon hpositive hthreshold (rounds + 1)) := by sorry
