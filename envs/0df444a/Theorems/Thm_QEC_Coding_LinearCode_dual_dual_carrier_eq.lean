-- Prove2me | Theorems.Thm_QEC_Coding_LinearCode_dual_dual_carrier_eq
-- name    : QEC.Coding.LinearCode.dual_dual_carrier_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:10:27.81036+00:00
-- url     : https://prove2.me/theorems/7675003e-85f9-492e-b424-142602961ef1
-- title:
--   Linear Code: dual dual carrier eq
-- statement:
--   Finite-dimensional orthogonal complementation is involutive.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Duality.lean#L26-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Duality.lean#L26-L37

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Duality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.LinearCode
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]

theorem QEC.Coding.LinearCode.dual_dual_carrier_eq (C : LinearCode F ι) : C.dual.dual.carrier = C.carrier := by sorry
