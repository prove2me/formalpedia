-- Prove2me | Theorems.Thm_QEC_Coding_LinearCode_eq_of_carrier_eq
-- name    : QEC.Coding.LinearCode.eq_of_carrier_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:10:32.994586+00:00
-- url     : https://prove2.me/theorems/2280a291-4a7c-4599-975e-99a4ce14d355
-- title:
--   Linear Code: eq of carrier eq
-- statement:
--   A linear code is determined by its carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Duality.lean#L19-L23
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Duality.lean#L19-L23

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Duality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.LinearCode
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]

theorem QEC.Coding.LinearCode.eq_of_carrier_eq {C D : LinearCode F ι} (h : C.carrier = D.carrier) : C = D := by sorry
