-- Prove2me | Theorems.Thm_QEC_Coding_LinearCode_le_dual_iff_le_dual
-- name    : QEC.Coding.LinearCode.le_dual_iff_le_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:13:57.832423+00:00
-- url     : https://prove2.me/theorems/9b8dd6de-1a3e-4902-a87a-11c0dbbaaafd
-- title:
--   Linear Code: le dual iff le dual
-- statement:
--   Dual containment between finite-coordinate linear codes is symmetric.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Definitions.lean#L206-L210
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Definitions.lean#L206-L210

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions
set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x
open QEC.Coding.LinearCode
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]

theorem QEC.Coding.LinearCode.le_dual_iff_le_dual (C D : LinearCode F ι) :
    D.carrier ≤ C.dual.carrier ↔ C.carrier ≤ D.dual.carrier := by sorry
