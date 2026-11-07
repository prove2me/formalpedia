-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_signedSwapWord_boundary2_dualData
-- name    : QEC.Coding.LiftedProduct.signedSwapWord_boundary2_dualData
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:37:18.853958+00:00
-- url     : https://prove2.me/theorems/cb91d0dd-34bf-49d0-bb6f-e56272723aa2
-- title:
--   Lifted Product: signed Swap Word boundary2 dual Data
-- statement:
--   The second boundary of the dual data becomes the transpose of the
--   original first boundary after the same signed coordinate exchange.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProductDuality.lean#L186-L227
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProductDuality.lean#L186-L227

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.signedSwapWord_boundary2_dualData
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [DecidableEq F]
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (w : Word F (C0Index aRow bRow G)) :
    signedSwapWord (boundary2 (dualData D) w) =
      wordLinearMapTranspose (boundary1 D) w := by sorry
