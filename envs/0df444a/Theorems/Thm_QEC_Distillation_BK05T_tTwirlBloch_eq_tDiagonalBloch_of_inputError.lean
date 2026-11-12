-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_tTwirlBloch_eq_tDiagonalBloch_of_inputError
-- name    : QEC.Distillation.BK05T.tTwirlBloch_eq_tDiagonalBloch_of_inputError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:25:48.263579+00:00
-- url     : https://prove2.me/theorems/476a3122-f272-4565-a7ef-6196169977e9
-- title:
--   BK05 T: t Twirl Bloch eq t Diagonal Bloch of input Error
-- statement:
--   The physical twirl's averaged Bloch vector is exactly the diagonal
--   T0/T1 vector at the density's measured input error.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L555-L569
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L555-L569

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

theorem QEC.Distillation.BK05T.tTwirlBloch_eq_tDiagonalBloch_of_inputError
    (rho : DensityOperator QubitSpace) (r : PauliAxis → Real)
    (hrho : rho.toOperator = blochProjector r) :
    tTwirlBloch r = tDiagonalBloch (tInputError rho) := by sorry
