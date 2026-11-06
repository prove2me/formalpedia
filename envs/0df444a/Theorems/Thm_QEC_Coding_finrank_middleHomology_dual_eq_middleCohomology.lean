-- Prove2me | Theorems.Thm_QEC_Coding_finrank_middleHomology_dual_eq_middleCohomology
-- name    : QEC.Coding.finrank_middleHomology_dual_eq_middleCohomology
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:38:12.185067+00:00
-- url     : https://prove2.me/theorems/1b441b09-f4a6-4976-8104-754bc825bbdb
-- title:
--   Coding: finrank middle Homology dual eq middle Cohomology
-- statement:
--   Middle homology of the finite-coordinate dual is definitionally the
--   middle cohomology of the original complex, hence their dimensions agree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/Duality.lean#L118-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/Duality.lean#L118-L123

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_ChainComplex_Duality
set_option autoImplicit false
open QEC QEC.Coding
universe u v
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {i0 i1 i2 : Type v}
variable [Fintype i0] [Fintype i1] [Fintype i2]

theorem QEC.Coding.finrank_middleHomology_dual_eq_middleCohomology
    (K : ChainComplexData F
      (Word F i0) (Word F i1) (Word F i2)) :
    Module.finrank F (dualChainComplex K).middleHomology =
      Module.finrank F K.middleCohomology := by sorry
