-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_verticalVertexSyndrome_ne_zero_of_localVertexMatrix_ne_zero
-- name    : QEC.Coding.TannerLiftedProduct.verticalVertexSyndrome_ne_zero_of_localVertexMatrix_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:37:48.113379+00:00
-- url     : https://prove2.me/theorems/914385e4-cab9-42f3-97e3-a09c2e44a76c
-- title:
--   Tanner Lifted Product: vertical Vertex Syndrome ne zero of local Vertex Matrix ne zero
-- statement:
--   Injectivity of the second generator map makes the vertex syndrome detect
--   every nonzero local coefficient block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L503-L522
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L503-L522

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
omit [Fintype F] [DecidableEq F] [Group G] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W] [Fintype R]
    [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.verticalVertexSyndrome_ne_zero_of_localVertexMatrix_ne_zero
    (h' : Matrix R' W F)
    (hinjective : Function.Injective
      (fun u : Word F R' => h'.transpose.mulVec u))
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (hv : localVertexMatrix c v ≠ 0) :
    verticalVertexSyndrome h' c v ≠ 0 := by sorry
