-- Prove2me | Theorems.Thm_QEC_Coding_LinearCode_mem_carrier
-- name    : QEC.Coding.LinearCode.mem_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:13:59.313824+00:00
-- url     : https://prove2.me/theorems/54e9c390-fd45-499b-a7ae-25f946f8c71e
-- title:
--   Linear Code: mem carrier
-- statement:
--   Membership in a linear code is membership in its carrier submodule.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Definitions.lean#L160-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Definitions.lean#L160-L162

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions
import Theorems.Thm_QEC_Semantics_QuantumCode_mem_carrier

set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x
open QEC.Coding.LinearCode
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]

theorem QEC.Coding.LinearCode.mem_carrier (C : LinearCode F ι) (x : Word F ι) :
    x ∈ C.carrier ↔ x ∈ (C : Submodule F (Word F ι)) := by sorry
