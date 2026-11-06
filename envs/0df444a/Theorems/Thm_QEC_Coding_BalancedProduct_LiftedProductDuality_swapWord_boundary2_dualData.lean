-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_swapWord_boundary2_dualData
-- name    : QEC.Coding.BalancedProduct.LiftedProductDuality.swapWord_boundary2_dualData
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:06:54.995505+00:00
-- url     : https://prove2.me/theorems/4970a94c-9ab3-4bbb-88bc-9ea6f0823834
-- title:
--   Lifted Product Duality: swap Word boundary2 dual Data
-- statement:
--   The second dual boundary becomes the transpose of the original first
--   boundary after exchanging the middle blocks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LiftedProductDuality.lean#L172-L212
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LiftedProductDuality.lean#L172-L212

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LiftedProductDuality
open QEC.Coding
universe u v

theorem QEC.Coding.BalancedProduct.LiftedProductDuality.swapWord_boundary2_dualData
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : LiftedProduct.Data (ZMod 2) G aRow aCol bRow bCol)
    (w : Word (ZMod 2) (LiftedProduct.C0Index aRow bRow G)) :
    swapWord (LiftedProduct.boundary2 (dualData D) w) =
      wordLinearMapTranspose (LiftedProduct.boundary1 D) w := by sorry
