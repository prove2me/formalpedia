-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_NoisyInput_aBasisObservable_eq_sourceAObservable
-- name    : QEC.Distillation.BK15.NoisyInput.aBasisObservable_eq_sourceAObservable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T01:07:43.65423+00:00
-- url     : https://prove2.me/theorems/cf512de6-7364-4b4a-acc4-f3f0755485d9
-- title:
--   Noisy Input: a Basis Observable eq source AObservable
-- statement:
--   The transported observable is the literal source `A = (X + Y) / sqrt(2)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/NoisyInput.lean#L291-L294
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/NoisyInput.lean#L291-L294

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_FifteenQubitH_NoisyInput
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.NoisyInput
open Semantics Semantics.Qubit
open OneQubitMagic
open Coding.PauliSymplectic
open scoped BigOperators TensorProduct
universe u v w
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.BK15.NoisyInput.aBasisObservable_eq_sourceAObservable :
    aBasisObservable = sourceAObservable := by sorry
