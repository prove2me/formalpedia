-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Recurrence_accepted_negativeA_weight_eq_l2LogicalCoset_wordSum
-- name    : QEC.Distillation.BK15.Recurrence.accepted_negativeA_weight_eq_l2LogicalCoset_wordSum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T04:16:21.855336+00:00
-- url     : https://prove2.me/theorems/25148262-ba9d-46bb-a7bc-c3017f903038
-- title:
--   Recurrence: accepted negative A weight eq l2 Logical Coset word Sum
-- statement:
--   The accepted physical branch, decoded by the total CSS decoder and tested
--   against the literal negative-A projector, is exactly the nontrivial `L2`
--   logical-coset word numerator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean#L2249-L2274
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean#L2249-L2274

import Definitions.Def_QEC_Distillation_FifteenQubitH_Protocol
import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Recurrence
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open NoisyInput Protocol
open scoped BigOperators TensorProduct
set_option linter.constructorNameAsVariable false

theorem QEC.Distillation.BK15.Recurrence.accepted_negativeA_weight_eq_l2LogicalCoset_wordSum
    (epsilon : BK15Epsilon) :
    acceptedNegativeAWeight epsilon =
      ∑ word ∈ l2LogicalCosetWords, bk15WordWeight epsilon word := by sorry
