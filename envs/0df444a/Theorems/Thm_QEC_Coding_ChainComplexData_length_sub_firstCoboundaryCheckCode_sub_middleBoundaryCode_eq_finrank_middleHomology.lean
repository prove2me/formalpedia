-- Prove2me | Theorems.Thm_QEC_Coding_ChainComplexData_length_sub_firstCoboundaryCheckCode_sub_middleBoundaryCode_eq_finrank_middleHomology
-- name    : QEC.Coding.ChainComplexData.length_sub_firstCoboundaryCheckCode_sub_middleBoundaryCode_eq_finrank_middleHomology
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:33:21.500725+00:00
-- url     : https://prove2.me/theorems/79b65e4f-08b5-4f2a-9713-09e856d65a3d
-- title:
--   Chain Complex Data: length sub first Coboundary Check Code sub middle Boundary Code eq finrank middle Homology
-- statement:
--   For binary finite-coordinate chain-complex data, the CSS exponent obtained from
--   the coboundary and boundary check dimensions is the middle-homology dimension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Definitions.lean#L740-L758
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Definitions.lean#L740-L758

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions
set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x
open QEC.Coding.ChainComplexData
variable {F : Type u} {ι : Type v} {C0 C2 : Type (max u v)} [Field F] [Fintype F]
    [Fintype ι] [AddCommGroup C0] [Module F C0] [AddCommGroup C2] [Module F C2]

theorem QEC.Coding.ChainComplexData.length_sub_firstCoboundaryCheckCode_sub_middleBoundaryCode_eq_finrank_middleHomology
    {ι κ lambda : Type u} [Fintype ι] [Fintype κ] [Fintype lambda]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) κ) (Word (ZMod 2) ι)
      (Word (ZMod 2) lambda)) :
    Length (ZMod 2) ι
      - Dimension K.firstCoboundaryCheckCode
      - Dimension K.middleBoundaryCode =
    Module.finrank (ZMod 2) K.middleHomology := by sorry
