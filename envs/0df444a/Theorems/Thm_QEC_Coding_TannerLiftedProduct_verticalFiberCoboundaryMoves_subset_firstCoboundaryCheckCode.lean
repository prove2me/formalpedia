-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_verticalFiberCoboundaryMoves_subset_firstCoboundaryCheckCode
-- name    : QEC.Coding.TannerLiftedProduct.verticalFiberCoboundaryMoves_subset_firstCoboundaryCheckCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:39:39.23301+00:00
-- url     : https://prove2.me/theorems/0b2fb10c-805f-408f-b154-a758cac8d741
-- title:
--   Tanner Lifted Product: vertical Fiber Coboundary Moves subset first Coboundary Check Code
-- statement:
--   Every vertical fiber move is a genuine first coboundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1649-L1658
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1649-L1658

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

theorem QEC.Coding.TannerLiftedProduct.verticalFiberCoboundaryMoves_subset_firstCoboundaryCheckCode
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (m : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hm : m ∈ verticalFiberCoboundaryMoves label h g') :
    m ∈ (chainComplex label h g').firstCoboundaryCheckCode.carrier := by sorry
