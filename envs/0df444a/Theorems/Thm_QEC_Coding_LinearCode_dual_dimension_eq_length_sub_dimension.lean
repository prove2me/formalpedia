-- Prove2me | Theorems.Thm_QEC_Coding_LinearCode_dual_dimension_eq_length_sub_dimension
-- name    : QEC.Coding.LinearCode.dual_dimension_eq_length_sub_dimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:17:13.108505+00:00
-- url     : https://prove2.me/theorems/ee57049c-f7fc-4d2c-b4ad-690872a02870
-- title:
--   Linear Code: dual dimension eq length sub dimension
-- statement:
--   The dual of a finite-coordinate linear code has dimension equal to ambient
--   length minus the dimension of the code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Definitions.lean#L327-L340
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Definitions.lean#L327-L340

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions
set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x
open QEC.Coding.LinearCode
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]

theorem QEC.Coding.LinearCode.dual_dimension_eq_length_sub_dimension (C : LinearCode F ι) :
    Dimension C.dual = Length F ι - Dimension C := by sorry
