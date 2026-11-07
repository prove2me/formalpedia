-- Prove2me | Theorems.Thm_QEC_Coding_LinearCode_dual_sup_carrier_eq
-- name    : QEC.Coding.LinearCode.dual_sup_carrier_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:10:38.532623+00:00
-- url     : https://prove2.me/theorems/1e0a917d-562a-4c7f-87c2-04c4597df14f
-- title:
--   Linear Code: dual sup carrier eq
-- statement:
--   The dual of a sum is the intersection of the duals.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Duality.lean#L44-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Duality.lean#L44-L60

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Duality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.LinearCode
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]

theorem QEC.Coding.LinearCode.dual_sup_carrier_eq (C D : LinearCode F ι) :
    ({ carrier := C.carrier ⊔ D.carrier } : LinearCode F ι).dual.carrier =
      C.dual.carrier ⊓ D.dual.carrier := by sorry
