-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_localVertexCosetLeaderMatrix_productKernel
-- name    : QEC.Coding.TannerLiftedProduct.localVertexCosetLeaderMatrix_productKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:35:10.977476+00:00
-- url     : https://prove2.me/theorems/b6ad1ec6-a0cb-40c8-bd23-b989092fb5c9
-- title:
--   Tanner Lifted Product: local Vertex Coset Leader Matrix product Kernel
-- statement:
--   The local coset-leader matrix is an actual word of the product kernel
--   used by the PK22 expansion hypothesis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L539-L551
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L539-L551

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
omit [Group G] [Fintype G] [DecidableEq G]
    [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.localVertexCosetLeaderMatrix_productKernel
    (h : Matrix R W F) (hRank : h.rank = Fintype.card R)
    (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) :
    ProductExpansion.ProductKernel h
      (ProductExpansion.generatorImageParityCheck h')
      (localVertexCosetLeaderMatrix h hRank h' c v) := by sorry
