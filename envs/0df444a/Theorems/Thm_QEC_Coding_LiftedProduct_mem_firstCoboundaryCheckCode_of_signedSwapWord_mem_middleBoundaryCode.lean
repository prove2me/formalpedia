-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_mem_firstCoboundaryCheckCode_of_signedSwapWord_mem_middleBoundaryCode
-- name    : QEC.Coding.LiftedProduct.mem_firstCoboundaryCheckCode_of_signedSwapWord_mem_middleBoundaryCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:13:26.988196+00:00
-- url     : https://prove2.me/theorems/ce97fb90-586c-489c-a587-fd8b85b0a590
-- title:
--   Lifted Product: mem first Coboundary Check Code of signed Swap Word mem middle Boundary Code
-- statement:
--   If the signed dual word is a boundary, the original word is an original
--   coboundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProductDuality.lean#L249-L276
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProductDuality.lean#L249-L276

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.mem_firstCoboundaryCheckCode_of_signedSwapWord_mem_middleBoundaryCode
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [DecidableEq F]
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (z : Word F (QubitIndex aRow aCol bRow bCol G))
    (hz : signedSwapWord z ∈
      (chainComplex (dualData D)).middleBoundaryCode.carrier) :
    z ∈ (chainComplex D).firstCoboundaryCheckCode.carrier := by sorry
