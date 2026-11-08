-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_localVertexCosetLeaderMatrix_ne_zero
-- name    : QEC.Coding.TannerLiftedProduct.localVertexCosetLeaderMatrix_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:35:56.211164+00:00
-- url     : https://prove2.me/theorems/b4b17a66-abd6-4810-b0de-511f4f78a81c
-- title:
--   Tanner Lifted Product: local Vertex Coset Leader Matrix ne zero
-- statement:
--   At an active vertex, injectivity of the second generator map makes the
--   local product-kernel witness nonzero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L557-L574
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L557-L574

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
omit [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [DecidableEq W] [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.localVertexCosetLeaderMatrix_ne_zero
    (h : Matrix R W F) (hRank : h.rank = Fintype.card R)
    (h' : Matrix R' W F)
    (hinjective : Function.Injective
      (fun u : Word F R' => h'.transpose.mulVec u))
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (hv : localVertexMatrix c v ≠ 0) :
    localVertexCosetLeaderMatrix h hRank h' c v ≠ 0 := by sorry
