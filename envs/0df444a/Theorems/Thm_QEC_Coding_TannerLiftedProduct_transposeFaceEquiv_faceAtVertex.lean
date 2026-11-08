-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_transposeFaceEquiv_faceAtVertex
-- name    : QEC.Coding.TannerLiftedProduct.transposeFaceEquiv_faceAtVertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:42:14.600233+00:00
-- url     : https://prove2.me/theorems/ba959f9f-9ac8-42a3-a3bf-df7b70f3c260
-- title:
--   Tanner Lifted Product: transpose Face Equiv face At Vertex
-- statement:
--   The face incident to a vertex is carried to the face with exchanged local
--   directions at the transposed vertex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L317-L327
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L317-L327

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
omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W] [Fintype R]
    [DecidableEq R] [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.transposeFaceEquiv_faceAtVertex
    (label targetLabel : W → G) (inverseDirection : W ≃ W)
    (hInverse : ∀ a, targetLabel (inverseDirection a) = (label a)⁻¹)
    (v : VertexIndex G) (a b : W) :
    transposeFaceEquiv inverseDirection (faceAtVertex label v a b) =
      faceAtVertex targetLabel (transposeVertexEquiv v)
        (inverseDirection b) (inverseDirection a) := by sorry
