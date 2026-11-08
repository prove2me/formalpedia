-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_generatorImageParityCheck_mul_verticalVertexSyndrome_eq_zero
-- name    : QEC.Coding.TannerLiftedProduct.generatorImageParityCheck_mul_verticalVertexSyndrome_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:37:52.588369+00:00
-- url     : https://prove2.me/theorems/70b6f636-fad4-4e70-9eb5-66499383406f
-- title:
--   Tanner Lifted Product: generator Image Parity Check mul vertical Vertex Syndrome eq zero
-- statement:
--   The parity check presenting the second generator image kills the entire
--   distinguished-vertex syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L481-L496
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L481-L496

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [DecidableEq F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype R] [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.generatorImageParityCheck_mul_verticalVertexSyndrome_eq_zero
    (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) :
    ProductExpansion.generatorImageParityCheck h' *
        verticalVertexSyndrome h' c v = 0 := by sorry
