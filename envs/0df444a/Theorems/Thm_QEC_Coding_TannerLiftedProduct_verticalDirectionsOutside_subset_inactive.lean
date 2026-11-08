-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_verticalDirectionsOutside_subset_inactive
-- name    : QEC.Coding.TannerLiftedProduct.verticalDirectionsOutside_subset_inactive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:39:54.408215+00:00
-- url     : https://prove2.me/theorems/730086b2-887e-4487-8481-9c0a8690bfdb
-- title:
--   Tanner Lifted Product: vertical Directions Outside subset inactive
-- statement:
--   Directions outside a set containing every active vertex are inactive in
--   the coefficient sense required by the local-star proof.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L183-L199
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L183-L199

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Fintype F] [DecidableEq W] [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.verticalDirectionsOutside_subset_inactive
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (L : Finset (VertexIndex G))
    (hActive : vertexBlockSupport c ⊆ L) (v : VertexIndex G) :
    verticalDirectionsOutside label L v ⊆
      verticalInactiveDirections label c v := by sorry
