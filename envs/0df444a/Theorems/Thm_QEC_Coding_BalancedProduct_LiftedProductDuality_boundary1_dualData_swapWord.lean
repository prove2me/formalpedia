-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_boundary1_dualData_swapWord
-- name    : QEC.Coding.BalancedProduct.LiftedProductDuality.boundary1_dualData_swapWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:06:52.977138+00:00
-- url     : https://prove2.me/theorems/3d29a969-be2a-40c7-9e26-2cac24df0df5
-- title:
--   Lifted Product Duality: boundary1 dual Data swap Word
-- statement:
--   The first dual boundary is the transpose of the original second boundary,
--   after exchanging the middle blocks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LiftedProductDuality.lean#L112-L168
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LiftedProductDuality.lean#L112-L168

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LiftedProductDuality
open QEC.Coding
universe u v

theorem QEC.Coding.BalancedProduct.LiftedProductDuality.boundary1_dualData_swapWord
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : LiftedProduct.Data (ZMod 2) G aRow aCol bRow bCol)
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol bRow bCol G)) :
    LiftedProduct.boundary1 (dualData D) (swapWord z) =
      wordLinearMapTranspose (LiftedProduct.boundary2 D) z := by sorry
