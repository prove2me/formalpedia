-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_transposeTannerWord_add
-- name    : QEC.Coding.TannerLiftedProduct.transposeTannerWord_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:41:49.335346+00:00
-- url     : https://prove2.me/theorems/d863a8a7-fc8d-4e09-b6c7-423c8c273780
-- title:
--   Tanner Lifted Product: transpose Tanner Word add
-- statement:
--   The Tanner Lifted Product construction uses the transpose Tanner Word add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L527-L537
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L527-L537

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerTranspose
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Fintype F] [Fintype G] [DecidableEq G] [Fintype W] [DecidableEq W]
    [DecidableEq F] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.transposeTannerWord_add
    (inverseDirection : W ≃ W)
    (z z' : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    transposeTannerWord inverseDirection (z + z') =
      transposeTannerWord inverseDirection z +
        transposeTannerWord inverseDirection z' := by sorry
