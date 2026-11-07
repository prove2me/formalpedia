-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_boundary1_dualData_signedSwapWord
-- name    : QEC.Coding.LiftedProduct.boundary1_dualData_signedSwapWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:37:39.622178+00:00
-- url     : https://prove2.me/theorems/767a0913-0acc-42a3-9b3e-9b32386f2e69
-- title:
--   Lifted Product: boundary1 dual Data signed Swap Word
-- statement:
--   The first boundary of the dual data is the transpose of the original
--   second boundary after signed middle-coordinate exchange.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProductDuality.lean#L127-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProductDuality.lean#L127-L182

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.boundary1_dualData_signedSwapWord
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [DecidableEq F]
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (z : Word F (QubitIndex aRow aCol bRow bCol G)) :
    boundary1 (dualData D) (signedSwapWord z) =
      wordLinearMapTranspose (boundary2 D) z := by sorry
