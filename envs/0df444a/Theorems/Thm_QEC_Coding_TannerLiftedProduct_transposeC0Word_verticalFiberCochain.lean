-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_transposeC0Word_verticalFiberCochain
-- name    : QEC.Coding.TannerLiftedProduct.transposeC0Word_verticalFiberCochain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:42:36.755525+00:00
-- url     : https://prove2.me/theorems/e0c93582-71f5-41d4-90f1-cb39e7a82a30
-- title:
--   Tanner Lifted Product: transpose C0 Word vertical Fiber Cochain
-- statement:
--   The Tanner Lifted Product construction uses the transpose C0 Word vertical Fiber Cochain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L593-L645
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L593-L645

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
omit [Fintype F] [DecidableEq F] [Fintype G] [Fintype W]
    [DecidableEq W] [DecidableEq R] [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.transposeC0Word_verticalFiberCochain
    (inverseDirection : W ≃ W) (edge : VerticalEdgeIndex W G)
    (u : Word F R) :
    transposeC0Word inverseDirection (verticalFiberCochain edge u) =
      horizontalFiberChain (transposeVerticalEdge inverseDirection edge) u := by sorry
