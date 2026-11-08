-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_horizontalFiberBoundaryMoves_subset_middleBoundaryCode
-- name    : QEC.Coding.TannerLiftedProduct.horizontalFiberBoundaryMoves_subset_middleBoundaryCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:39:22.709403+00:00
-- url     : https://prove2.me/theorems/255926e7-0d0f-43c1-adc6-38552bb17649
-- title:
--   Tanner Lifted Product: horizontal Fiber Boundary Moves subset middle Boundary Code
-- statement:
--   Every horizontal fiber move is a genuine middle boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1637-L1646
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1637-L1646

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

theorem QEC.Coding.TannerLiftedProduct.horizontalFiberBoundaryMoves_subset_middleBoundaryCode
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (m : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hm : m ∈ horizontalFiberBoundaryMoves label h g') :
    m ∈ (chainComplex label h g').middleBoundaryCode.carrier := by sorry
