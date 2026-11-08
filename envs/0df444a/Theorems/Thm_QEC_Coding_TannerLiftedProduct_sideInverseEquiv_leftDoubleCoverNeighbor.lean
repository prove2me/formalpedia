-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_sideInverseEquiv_leftDoubleCoverNeighbor
-- name    : QEC.Coding.TannerLiftedProduct.sideInverseEquiv_leftDoubleCoverNeighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:06:06.706083+00:00
-- url     : https://prove2.me/theorems/b3709682-9ecc-4ccf-9ccb-8442e23361c3
-- title:
--   Tanner Lifted Product: side Inverse Equiv left Double Cover Neighbor
-- statement:
--   Switching sides and inverting conjugates left multiplication to right
--   multiplication.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L151-L158
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L151-L158

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
omit [Fintype G] [DecidableEq G] [Fintype W] [DecidableEq W]

theorem QEC.Coding.TannerLiftedProduct.sideInverseEquiv_leftDoubleCoverNeighbor
    (label : W → G) (x : Fin 2 × G) (a : W) :
    sideInverseEquiv (leftDoubleCoverNeighbor label x a) =
      rightDoubleCoverNeighbor label (sideInverseEquiv x) a := by sorry
