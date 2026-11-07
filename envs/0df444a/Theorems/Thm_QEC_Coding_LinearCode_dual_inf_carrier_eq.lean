-- Prove2me | Theorems.Thm_QEC_Coding_LinearCode_dual_inf_carrier_eq
-- name    : QEC.Coding.LinearCode.dual_inf_carrier_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:40:51.728239+00:00
-- url     : https://prove2.me/theorems/ca1cba1c-fb19-44bf-845e-02f1b1edb05a
-- title:
--   Linear Code: dual inf carrier eq
-- statement:
--   The dual of an intersection is the sum of the duals.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Duality.lean#L63-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Duality.lean#L63-L71

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Duality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.LinearCode
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]

theorem QEC.Coding.LinearCode.dual_inf_carrier_eq (C D : LinearCode F ι) :
    ({ carrier := C.carrier ⊓ D.carrier } : LinearCode F ι).dual.carrier =
      C.dual.carrier ⊔ D.dual.carrier := by sorry
