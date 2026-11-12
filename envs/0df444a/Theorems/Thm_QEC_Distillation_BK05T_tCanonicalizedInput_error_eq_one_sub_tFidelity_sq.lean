-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_tCanonicalizedInput_error_eq_one_sub_tFidelity_sq
-- name    : QEC.Distillation.BK05T.tCanonicalizedInput_error_eq_one_sub_tFidelity_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:25:52.360238+00:00
-- url     : https://prove2.me/theorems/c55e6af9-a2df-4e4f-9825-4ea7b6761cb4
-- title:
--   BK05 T: t Canonicalized Input error eq one sub t Fidelity sq
-- statement:
--   After finite Clifford normalization, the BK05 input error is exactly one
--   minus the squared maximum T fidelity of the original density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L825-L829
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L825-L829

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

theorem QEC.Distillation.BK05T.tCanonicalizedInput_error_eq_one_sub_tFidelity_sq
    (rho : DensityOperator QubitSpace) :
    tInputError (tCanonicalizedInput rho) = 1 - tFidelity rho ^ 2 := by sorry
