-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_transposeVertexEquiv_horizontalEndpoint
-- name    : QEC.Coding.TannerLiftedProduct.transposeVertexEquiv_horizontalEndpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:41:26.524344+00:00
-- url     : https://prove2.me/theorems/e80d689a-e854-40e5-a562-89ef938592e5
-- title:
--   Tanner Lifted Product: transpose Vertex Equiv horizontal Endpoint
-- statement:
--   Every horizontal endpoint vertex is carried to the corresponding vertical
--   endpoint vertex in the exchanged product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L334-L351
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L334-L351

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

theorem QEC.Coding.TannerLiftedProduct.transposeVertexEquiv_horizontalEndpoint
    (label targetLabel : W → G) (inverseDirection : W ≃ W)
    (hInverse : ∀ a, targetLabel (inverseDirection a) = (label a)⁻¹)
    (v : VertexIndex G) (a : W) (endpointSide : Fin 2) :
    transposeVertexEquiv
        (match v with
        | (side, side', g) =>
            (endpointSide, side',
              g * (doubleCoverVoltage label side a)⁻¹ *
                doubleCoverVoltage label endpointSide a)) =
      (match transposeVertexEquiv v with
      | (side', side, g) =>
          (side', endpointSide,
            doubleCoverVoltage targetLabel endpointSide (inverseDirection a) *
              (doubleCoverVoltage targetLabel side (inverseDirection a))⁻¹ * g)) := by sorry
