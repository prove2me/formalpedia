-- Prove2me | Theorems.Thm_QEC_Coding_LinearCode_symplecticForm_x_zero_zero_z_eq_zero_of_mem_dual
-- name    : QEC.Coding.LinearCode.symplecticForm_x_zero_zero_z_eq_zero_of_mem_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:16:47.537033+00:00
-- url     : https://prove2.me/theorems/065fe18a-3f11-4860-9eec-cd506b1fb8f7
-- title:
--   Linear Code: symplectic Form x zero zero z eq zero of mem dual
-- statement:
--   Codewords commute with words from the dual in the CSS X/Z symplectic shape used
--   by later stabilizer and CSS constructions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Definitions.lean#L549-L554
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Definitions.lean#L549-L554

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions
set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x
open QEC.Coding.LinearCode
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]

theorem QEC.Coding.LinearCode.symplecticForm_x_zero_zero_z_eq_zero_of_mem_dual (C : LinearCode F ι)
    {x z : Word F ι} (hx : x ∈ C.carrier) (hz : z ∈ C.dual.carrier) :
    symplecticForm ({ xPart := x, zPart := 0 } : SymplecticVector F ι)
        ({ xPart := 0, zPart := z } : SymplecticVector F ι) = 0 := by sorry
