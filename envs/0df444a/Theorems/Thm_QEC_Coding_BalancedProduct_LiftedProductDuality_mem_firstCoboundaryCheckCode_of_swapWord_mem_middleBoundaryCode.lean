-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_mem_firstCoboundaryCheckCode_of_swapWord_mem_middleBoundaryCode
-- name    : QEC.Coding.BalancedProduct.LiftedProductDuality.mem_firstCoboundaryCheckCode_of_swapWord_mem_middleBoundaryCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:39:30.613811+00:00
-- url     : https://prove2.me/theorems/fa33590d-a5fa-4f12-8904-1da6b57d14fd
-- title:
--   Lifted Product Duality: mem first Coboundary Check Code of swap Word mem middle Boundary Code
-- statement:
--   If the exchanged dual word is a boundary, the original word is an
--   original coboundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LiftedProductDuality.lean#L234-L259
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LiftedProductDuality.lean#L234-L259

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LiftedProductDuality
open QEC.Coding
universe u v

theorem QEC.Coding.BalancedProduct.LiftedProductDuality.mem_firstCoboundaryCheckCode_of_swapWord_mem_middleBoundaryCode
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : LiftedProduct.Data (ZMod 2) G aRow aCol bRow bCol)
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol bRow bCol G))
    (hz : swapWord z ∈
      (LiftedProduct.chainComplex (dualData D)).middleBoundaryCode.carrier) :
    z ∈ (LiftedProduct.chainComplex D).firstCoboundaryCheckCode.carrier := by sorry
