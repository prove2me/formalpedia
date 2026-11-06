-- Prove2me | Theorems.Thm_QEC_Coding_ChainComplexData_finrank_middleHomology_eq
-- name    : QEC.Coding.ChainComplexData.finrank_middleHomology_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:33:15.95307+00:00
-- url     : https://prove2.me/theorems/1bada8f2-6453-40fa-b14b-b3318cb83b59
-- title:
--   Chain Complex Data: finrank middle Homology eq
-- statement:
--   The middle-homology dimension is the cycle dimension minus the boundary
--   dimension, computed as the quotient by the actual boundary submodule in cycles.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Definitions.lean#L695-L703
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Definitions.lean#L695-L703

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions
set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x
open QEC.Coding.ChainComplexData
variable {F : Type u} {ι : Type v} {C0 C2 : Type (max u v)} [Field F] [Fintype F]
    [Fintype ι] [AddCommGroup C0] [Module F C0] [AddCommGroup C2] [Module F C2]

theorem QEC.Coding.ChainComplexData.finrank_middleHomology_eq
    (K : ChainComplexData F C0 (Word F ι) C2) :
    Module.finrank F K.middleHomology =
      Dimension K.middleCycleCode - Dimension K.middleBoundaryCode := by sorry
