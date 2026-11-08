-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_doubleCoverSideSwapEquiv_rightDoubleCoverNeighbor
-- name    : QEC.Coding.TannerLiftedProduct.doubleCoverSideSwapEquiv_rightDoubleCoverNeighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:43:10.377196+00:00
-- url     : https://prove2.me/theorems/0249d935-57c3-4fdb-a3d4-822abe0ae1d5
-- title:
--   Tanner Lifted Product: double Cover Side Swap Equiv right Double Cover Neighbor
-- statement:
--   The Tanner Lifted Product construction uses the double Cover Side Swap Equiv right Double Cover Neighbor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L946-L954
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L946-L954

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
omit [Field F] [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]
    [Fintype W] [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.doubleCoverSideSwapEquiv_rightDoubleCoverNeighbor
    (label : W → G) (x : Fin 2 × G) (a : W) :
    doubleCoverSideSwapEquiv (rightDoubleCoverNeighbor label x a) =
      rightDoubleCoverNeighbor (inverseGeneratorLabel label)
        (doubleCoverSideSwapEquiv x) a := by sorry
